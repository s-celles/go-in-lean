# Feasibility of checking Go compiler SSA rewrite rules in Lean (Phase 6)

## What the Go compiler actually does

* Optimisations are expressed as rewrite rules in
  `src/cmd/compile/internal/ssa/_gen/*.rules`; `generic.rules` (2,845 lines
  in go1.25.5, sha256 `d3be0703…`) is architecture-independent, the
  `<ARCH>.rules` files lower to machine ops. `rulegen` generates
  `rewritegeneric.go` etc. ([README](https://go.dev/src/cmd/compile/internal/ssa/README)).
* Rule syntax: `(Op <type> [auxint] {aux} args…) && cond => (Op' …)`. The
  first matching rule in file order wins; side conditions are Go
  expressions over AuxInts and helper predicates (`isPowerOfTwo`, `log64`,
  `umagic`, `isNonNegative`, `uaddOvf`, …) in `rewrite.go`.
* Values of width 8/16/32 are stored in `int64` AuxInts that must be
  sign-extended (`value.go`); several historical miscompiles were
  violations of exactly this invariant (#15175, #42753) or confusion about
  shift-amount width/sign (#64285, #79886, commit 8dcb3171).
* Testing today: `test/codegen` asm regexps, `cmd/compile/internal/test`
  execution tests (`constFold_test.go`, `shift_test.go`, `divconst_test.go`),
  `test/fixedbugs`. No formal check of the rules exists; the two external
  attempts (golang_tv with Alive2, mmcloughlin/ssarules with SMT2) were
  abandoned early (`docs/prior-art.md` §3).

## What was tried here (`GoInLean/Compiler/GenericRules.lean`)

Each rule is modelled as an equation between `BitVec` expressions under the
rule's side condition, with signedness carried by the opcode exactly as in
the compiler. Results (all kernel-checked, `bv_decide` where the audit says
so):

| Rule (generic.rules line) | Width | Result |
|---|---|---|
| `isPowerOfTwo(c)` ⇔ `c = 1 << k`, `k ≤ w-2` (bridging lemma for the rules below) | 8 | proved (`decide`); note `c > 0` is a *signed* test, so `1 << (w-1)` is excluded |
| `Mul n (Const c) && isPowerOfTwo(c) => Lsh n log(c)` (203-206) | 8 (all k), 64 (all k, algebraic) | proved |
| `Div8u n c && isPowerOfTwo(c) => Rsh8Ux64 n log(c)` (1013-1017) | 8, 32 (all k); 64 (k ∈ {1,5,63}) | proved; 64-bit symbolic divisor exceeds the SAT budget |
| `Mod8u n c && isPowerOfTwo(c) => And8 n (c-1)` (1293-1297) | 8, 32 (all k); 64 (k ∈ {5,63}) | proved |
| `Mod8 n c && isNonNegative(n) && isPowerOfTwo(c) => And8 n (c-1)` (1300) | 8 | proved, assuming `isNonNegative` implies `msb n = false` |
| `Div8 n c && isNonNegative(n) && isPowerOfTwo(c) => Rsh8Ux64` (1020) | 8 | proved, same assumption |
| signed `Div` by 2^k, 4-op sequence (1199-1214) | 8, 32 (all admissible k); 64 (k ∈ {1,5,32,62}) | proved; the variant admitting `k = w-1` was **refuted** (`n = MinInt`), confirming why the side condition excludes it |
| `Div x (Const -1<<w-1) => Rsh (And x (Neg x)) (w-1)` (1190, 1193) | 8, 64 | proved |
| `Div n c && c<0 && c != MinInt => Neg (Div n (-c))` (1182) | 8 | proved |
| `Lsh (Lsh x c) d && !uaddOvf(c,d) => Lsh x (c+d)` (455) | 8 | proved |
| `RshU (RshU x c) d && !uaddOvf(c,d)` (465-equivalent at 64) | 64 | proved |
| `Rsh8Ux64 (Rsh8x64 x _) 7 => Rsh8Ux64 x 7` (468) | 8 | proved |
| `Lsh (RshU x c) c => And x (-1 << c)`, `RshU (Lsh x c) c => And x (^0 >> c)` (477, 482) | 8 | proved |
| `(Lsh|RshU) _ c && c >= w => 0` | 64 | proved |
| `IsInBounds (RshU _ c) d && … => true` (257-266) | 8 | proved |
| `IsInBounds (Mod64u _ y) y => true` (255) | 64 | proved with `y ≠ 0` (needed: Lean's `x % 0 = x`; Go has already trapped) |
| `RshU (Const8 c) (Const64 d) => Const8 [int8(uint8(c) >> d)]` (233) | 8 | proved: value correct **and** AuxInt canonical |
| the Go 1.6 version of the same rule without re-sign-extension (#15175) | 8 | **refuted** (kernel-checked negation), reproducing the historical bug's witness `uint8(253) >> 0` |

Type-checking the file takes about 10 s; each `bv_decide` call is well under
the 10 s default budget except 64-bit *symbolic-divisor* division/modulo,
which times out and is replaced by constant-divisor instances. The
corresponding Go execution tests are `TestCompilerPow2Rules`,
`TestCompilerSignedDivPow2`, `TestCompilerShiftRules` and
`TestIssue15175Regression` in `go/tests/compiler_rules_test.go`.

## Generated constant-folding theorems (`scripts/rules_to_lean.py`)

A first version of the rule translator recommended below exists. It parses
`generic.rules` and, for every constant-folding rule of the shapes
`(OpN (ConstN [c]) (ConstN [d])) [&& d != 0] => (ConstN [expr])`,
`(OpN (ConstN [c])) => …`, `(OpNx64 (ConstN [c]) (Const64 [d])) => …`
and `(Trunc|ZeroExt|SignExt)AtoB`, emits a Lean theorem stating that the
rule's right-hand side, read with Go's *typed* AuxInt semantics
(`rewritegeneric.go` uses `auxIntToInt8 … int8ToAuxInt`, so `c+d` is `int8`
arithmetic), equals the generic operation's semantics in `OpSem.lean`
(hand-written from `genericOps.go`). Result for go1.25.5: 74 rules
translated and proved (`GoInLean/Compiler/GeneratedFolds.lean`, kernel-only;
most close by unfolding, shifts and divisions carry the content), 60
constant rules deliberately *not* translated and listed at the end of the
generated file (floating point, 128-bit multiply tuples, reassociation
with a variable operand, `ntz`/`nlz` mask elimination). CI checks that the
generated file is up to date with the pinned `generic.rules`.

What this checks is the agreement of two hand-written tables, the
Go-expression translation and `OpSem`, with the rule text. The value lies
in making every rule's meaning explicit and mechanically re-checkable when
`generic.rules` changes; a translation error would show up as a failed
proof, as happened during development with the shift-amount typing.

## What this does and does not establish

* It establishes that the *arithmetic content* of these rules is correct
  for all inputs of the given width under the modelled side conditions, and
  that the AuxInt representation invariant is preserved by the folded
  constant. It is a *rule-level* check, i.e. translation validation of the
  rewrite step itself, not of a particular compilation.
* It does **not** establish compiler correctness: the model does not
  include (i) the pattern matcher and rule ordering generated by `rulegen`,
  (ii) the static approximations behind side conditions such as
  `isNonNegative(n)` (facts/prove pass): a theorem assumes the semantic fact
  the approximation is meant to imply; (iii) panic semantics (division by
  zero, bounds checks are separate SSA ops whose insertion is not
  modelled); (iv) the per-architecture lowering where most recent shift
  miscompiles happened (`ARM64.rules`, `RISCV64.rules`); (v) memory, calls,
  control flow, and types other than integers; (vi) floating point.
* The `IsInBounds (Mod64u _ y) y` rule shows the typical pitfall of a naive
  model: without the `y ≠ 0` hypothesis the Lean statement is false, while
  the Go rule is sound because `Mod64u` by zero has already panicked.
  Modelling such control-dependent facts is where a faithful SSA semantics
  (with explicit panic edges) would be needed.

## Comparison with alternatives

| Approach | Strengths | Weaknesses for Go rules |
|---|---|---|
| Alive2-style translation validation (SMT, per compilation or per rule) | mature for LLVM, handles UB/poison precisely, found 47 LLVM bugs | Go has no LLVM-style UB; golang_tv lifted to LLVM IR and stalled on panics; SMT solver in the trusted base |
| Direct SMT (`ssarules` → SMT2) | cheap to generate from the rule DSL | parser/semantics of the DSL and of AuxInt conventions must be written anyway; abandoned |
| Lean `bv_decide` (this experiment) | kernel-checked certificate, same `BitVec` library as the stdlib models, counterexamples are concrete | SAT budget limits general multiplication/division (≥ 16-bit `*`, 64-bit `udiv` with non-constant divisor); each rule hand-translated |
| Go's own tests (`constFold_test`, `codegen`) | run the real compiler | only sampled inputs; no AuxInt invariant checks beyond `rulegen`'s syntactic ones |

## Feasibility verdict and recommended next step

A rule-level checker is feasible and useful for the *generic* arithmetic
rules: the `.rules` grammar is regular enough to parse, the AuxInt
conventions are documented, and bit-blasting handles shifts, masks,
additions, comparisons and constant multiplication/division at 64 bits.
The recommended next step is a translator from `generic.rules` to Lean
statements for the subset of rules whose side conditions are decidable
functions of AuxInts (constant folding, shift algebra, power-of-two
strength reduction, truncation/extension cancellation), batch-proved with
`bv_decide`, with every failure triaged exactly as stdlib counterexamples
are (Go reproducer compiled with the real compiler, `go tool compile -S`,
`test/codegen`-style assertion). Rules with `umagic`/`smagic` (multiplication
by magic constants) need either a longer SAT budget or an algebraic proof;
rules with `isNonNegative`/`uses == 1`/`config.*` conditions need the
fact-propagation semantics and should be out of scope for a first tool.
Architecture-specific lowering rules, where recent bugs cluster, require a
model of the machine operations' exact masking behaviour (e.g. ARM64 `LSL`
masks the amount modulo 64) and are a separate, larger project.
