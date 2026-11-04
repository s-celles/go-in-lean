# cedar-spec / cedar-drt — anatomy and lessons for go-in-lean

How Cedar (AWS) formalizes its policy language in Lean 4 and uses the
specification as an oracle *inside* the fuzz loop. Sources: the
[cedar-policy/cedar-spec](https://github.com/cedar-policy/cedar-spec)
repository (README, cedar-drt/README, cedar-lean-ffi/README, build scripts),
November 2026.

## 1. Structure

| Component | Role |
|---|---|
| `cedar-lean` | The Lean 4 formalization of Cedar (executable semantics + proofs), built with `lake build Cedar` |
| `cedar-lean-ffi` | **The bridge**: Rust bindings to the Lean spec; `build_lean_lib.sh` runs `lake build CedarFFI:static` (a static library with the Lean runtime embedded) |
| `cedar-drt` | `cargo fuzz` targets (libFuzzer): Rust-vs-Lean differential testing (DRT) + property-based testing (PBT) |
| `cedar-policy-generators` | Generators for schemas/entities/policies/requests via the `arbitrary` crate (host side, not Lean) |

## 2. The three technical decisions that make the Lean oracle practical

1. **Serialization rather than type marshalling.** The FFI does not convert
   Rust types into Lean types: Cedar structures travel as **Protobuf** (the
   protobuf feature of the Rust crate, the `CedarProto` target on the Lean
   side). The bridge only carries bytes. That is what keeps it maintainable:
   both sides evolve independently, and the contract is the schema.
2. **The Lean spec is *executable*.** The oracle does not invoke a proof at
   runtime: `lake build CedarFFI:static` compiles Cedar's operational semantics
   into native code through Lean's compiler, with the Lean runtime
   (`libleanshared.so`) linked statically. The proofs (decidability, theorems)
   guarantee upstream that the semantics being executed is the right one — the
   oracle is the *proven* semantics, evaluated.
3. **The generator lives on the host, not in Lean.** `cedar-policy-generators`
   produces the inputs (often "type-directed", i.e. shaped toward well-typed
   inputs — the counterpart of our typed chains). Lean is only the arbiter.
   It is the same separation as ours: class-targeted generation on the Python
   side, semantics on the Lean side.

## 3. The DRT loop

```
arbitrary/generator → input (policy, entities, request)
   → evaluation by the Rust implementation (cedar)
   → evaluation by the Lean spec (via protobuf + FFI)
   → divergence = bug (reduced, dumped as a regression test)
```

- About 18 targets: authorizer, evaluator, validator, entity/request
  validation, and the TPE family (partial evaluation: decisions, policy
  categorizations, residual expressions).
- `synthesize_tests.sh` is **not** a generator: it is the harness which, when
  `DUMP_TEST_DIR` is set, replays the corpus and **dumps** every input as a
  regression test. The "synthesis" comes from the fuzzing itself.
- Everything runs under `cargo fuzz` (libFuzzer) — a high in-process
  throughput, hence the FFI rather than a subprocess.

## 4. Translation for go-in-lean (refining J1)

The pattern transposed, from simplest to most faithful:

1. **Subprocess oracle (J1a, sufficient at our scale).** Our dominant cost is
   one Go build+run per seed (seconds), not millions of executions per second:
   there is no need for in-process FFI. A Lean executable
   (`lake build goinlean-oracle`) reads a serialized expression (an
   s-expression emitted by the generator next to the Go program) on stdin,
   evaluates it against `OpSem`/`GenericSem`, and prints the result — compared
   against the checksum of the real binary. The contract is the serialized
   shape, the equivalent of their protobuf.
2. **FFI oracle (J1b, if throughput ever justifies it).** Their exact scheme:
   a `:static` Lean target plus a minimal binary channel. Only worth building
   if the subprocess oracle ever becomes the bottleneck.
3. **Synthesized tests (J2).** Two meanings at Cedar, and we want both:
   (a) regression dumps from fuzzing (theirs) — our triage already does the
   equivalent; (b) our own addition: **generate at theorem boundaries** (the
   inputs where a model precondition flips truth value — where `bv_decide`
   produces its counterexamples) and inject those points as seeds and shapes.
   This is the point where go-in-lean goes beyond cedar-drt: their model does
   not steer generation, ours can.

What must be verified before J1 (model debt): does the executable semantics of
`OpSem`/`GenericSem` cover *every* operation the generator emits (otherwise the
oracle rejects valid programs), and does the model agree with the Go spec on
the corners already proven (the 13 `property.lean` findings recovered by the
oracle = the acceptance criterion of J1)?

## 5. Going further

- AWS Science blog: "How we built Cedar with automated reasoning and
  differential testing"; "Lean Into Verified Software Development".
- `Cedar.SymCC` (a target present in build_lean_lib.sh): their track toward
  symbolic analysis driven by the spec — worth a look if we ever want SMT
  counterexamples rather than plain evaluation.
