# Specification-driven differential fuzzing — vision and positioning

A study of the existing fuzzers (Mozilla Security, Project Zero, cedar-spec)
and the target architecture for go-in-lean: reuse the existing engines and
make formal semantics the added value — both as an oracle and as a producer
of test programs.

## 1. What the studied frameworks do

| Framework | Mechanism | What we keep for go-in-lean |
|---|---|---|
| [jsfunfuzz](https://github.com/MozillaSecurity/funfuzz)/[funfuzz](https://github.com/MozillaSecurity/funfuzz) | Grammar-based generation of JS function bodies, `--compare-jit` mode (interpreter/JIT/versions differential), Lithium reduction. | This *is already* our approach: shape-based generators plus the cross-configuration differential oracle (GODEBUG, GOARCH, optimized vs `-N`). Our added value lies elsewhere. |
| [Fuzzilli](https://github.com/googleprojectzero/fuzzilli) (NDSS 2023) | Coverage-guided over a **typed IR** (FuzzIL) + validity-preserving mutations + correctness properties; interpreter/JIT differential. | The typed IR: our generators already emerge as typed IRs (the typed chains of `simd_fuzz.py`, the IR of `metamorphic_fuzz.py`). Coverage guidance is a possible optimization, not a change of method — it compensates by brute force what semantic targeting does directly. |
| [cedar-drt](https://github.com/cedar-policy/cedar-spec/tree/main/cedar-drt) | **Differential fuzzing of the Rust implementation against the Lean spec** (DRT) + property-based testing (round trip, general); `build_lean_lib.sh` compiles the spec into a library called from the fuzz targets; `synthesize_tests.sh` synthesizes tests. | The exact pattern for our trajectory: the Lean spec becomes the **oracle in the loop** (not just an offline refutation tool) and a source of **synthesized tests**. See `docs/cedar-notes.md` for the full anatomy. |
| [dharma](https://github.com/MozillaSecurity/dharma)/Peach/ffuf | Context-free grammars, model-based, web fuzzing. | Out of domain (formats/protocols), no semantic oracle. |

Why not AFL++/libFuzzer/Atheris: they mutate bytes toward *crashes* on parsers.
Our target takes structured input (valid programs), pays a high cost per
execution (build+run), and its bugs are *silent* (wrong code) that no crash
reveals — a semantic oracle is indispensable. Our method is the one of
Csmith/jsfunfuzz: grammar-based generation plus differential testing. The track
record of the last three days (13 issues/CLs plus one build failure found by
class-targeted generation) argues for keeping semantic targeting as the
steering mechanism.

## 2. What go-in-lean already has (state 2026-11-03)

- Operational semantics: `GoInLean/Compiler/OpSem.lean`, `GenericSem.lean`
  (SSA op → semantics over bitvectors), `KnownBits.lean` (a known-bits
  analysis, the compiler's analogue).
- Translated rules: `GeneratedRules.lean`/`GeneratedFolds.lean` (lowering and
  constant folds generated from the `.rules`), with ARM64/AMD64/MIPS/PPC64/
  RISCV/S390X families.
- 13 `findings/*/property.lean`: every bug found, formalized as a Lean
  property.
- The existing workflow: theorem (documented behaviour) → proof (kernel,
  `bv_decide`) → failed proof = counterexample → a concrete Go test → run
  against the pinned toolchain. A refutation is never a Go bug until it
  reproduces in Go.
- The specialized per-domain generators: `metamorphic_fuzz.py` (integer
  overflows, conversions, late folds, x86 flags, late/bits/countvar/carry/
  branchy), `float_fuzz.py` (floats, conversions, FMA, `--late`),
  `bce_fuzz.py` (bounds-check elimination), `simd_fuzz.py` (SIMD chains) —
  exactly the listed zones: overflows, conversions, evaluation order, SSA
  optimizations, architecture differences.

What is missing for the "Lean as producer *and* oracle" vision:
1. the Lean oracle **inside** the fuzz loop (today the oracle is
   cross-configuration; Lean only intervenes upstream, at refutation);
2. **model-steered test synthesis** (today the model produces counterexamples
   of properties already written, not fuzz programs).

## 3. Target architecture

```
Lean model (OpSem, GenericSem, KnownBits, GeneratedRules)
   |
   |- (a) Oracle: GoInLean compiled into a library (the build_lean_lib.sh
   |      pattern of cedar-drt) -> semantic evaluation of a generated
   |      program, compared against the execution of the real binary.
   |
   |- (b) Producer: counterexamples and precondition boundaries
   |      (bv_decide / said) -> seeds and shapes for the generators
   |      (the fuzzer systematically attacks the zones where the theorems
   |      are tight: carry/borrow, mixed widths, chained folds, NaN, masks).
   |
   +- (c) Refutation: new lowering/fold rule translated (rules_to_lean.py)
          -> property -> failure = a new finding (the current loop, kept).

Specialized generators (per domain) -> Go programs
   -> oracle (a) + cross-configuration differential oracle (existing, kept)
   -> mismatch -> minimization -> finding -> issue/CL (the established workflow)
```

The two oracles complement each other: the cross-configuration one catches
divergences *between implementations* (and covers everything the model does
not formalize yet), the Lean oracle compares against the *documented
semantics* — it catches the classes where every implementation is wrong
together, invisible to the differential.

## 4. Milestones

1. **J1 — the cedar-drt pattern on our subset**: plug a Lean oracle into
   `metamorphic_fuzz.py --bits` (integers, `math/bits`, the already-modelled
   subset), as a **subprocess** first (a Lean executable that evaluates a
   serialized expression emitted by the generator — our dominant cost is the
   Go build, not the evaluation, so no need for the in-process FFI of
   cedar-lean-ffi; see `docs/cedar-notes.md` for the exact pattern and the
   FFI variant). Success criterion: the fuzzer flags the known
   counterexamples (the 13 `property.lean` findings must be recovered by the
   seeds) with nothing spurious.
2. **J2 — steered synthesis**: `synthesize_tests`, cedar-drt style: generate
   programs at theorem boundaries (the points where a precondition flips) and
   inject them as seeds and shapes of the generators. Criterion: a higher
   density of semantically hot shapes per seed than random generation
   (measured as flags per 1000 seeds).
3. **J3 — extend the model** to the uncovered zones: the semantics of SIMD
   masks (SIMD-MASKED-SHIFT-NOIMM showed how young the domain is), then
   floats. Every model extension is a new domain for (a) and (b).
4. **J4 (optional) — coverage guidance**: if class-targeted generation
   saturates, add compiler coverage feedback to the generators
   (Fuzzilli-style, but over our typed IRs).

## 5. Positioning

Do not build a generalist competitor to AFL++: fuzzing engines and corpora
already exist. The contribution of go-in-lean is the formal semantics — a
bit-precise model of Go's lowering rules, kernel-checked proofs, and the
exploitation of the model as an oracle and as a generation strategist. It is
the meeting of cedar-drt (a Lean spec as an implementation oracle) with the
Csmith/jsfunfuzz tradition (program generation), applied to a compiler.
