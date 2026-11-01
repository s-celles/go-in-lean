# Research report: go-in-lean, iteration 1 (2026-11-01)

## 1. Executive summary

go-in-lean asks whether AI-assisted formal modelling in Lean 4 can
*systematically* and *trustworthily* find correctness defects in Go
implementations. In this first iteration we built the full pipeline and ran
it over all of `math/bits`, selected `slices`/`sort` functions and a set of
Go compiler SSA rewrite rules:

* **46 properties registered**, **38 proved in the model** (187 audited
  theorems: 67 via `bv_decide`, 120 kernel-only, zero `sorry`, zero
  `native_decide`), **5 inconclusive** (2 for SAT budget: 64-bit
  multiplication/division; 3 for the aliasing-aware slice functions, which
  are checked exhaustively on a bounded domain but not proved in general),
  **1 model-level counterexample** (negative control), **2 known issues
  reproduced** (golang/go#54255, golang/go#15175).
* **No new Go bug was found.** Everything proved and tested in `math/bits`,
  `slices.Compact/Index/Contains`, `sort.Search` and the modelled compiler
  rules behaves as documented in go1.25.5.
* **The pipeline detects defects**: 5 deliberately wrong models are refuted by
  `bv_decide` and every counterexample reproduces as a failing Go test
  against the Go mutant while the real function passes.
* **The pipeline detects its own mistakes**: 4 of the first-draft Lean models
  were wrong (Go vs Lean operator precedence) and 2 of the first-draft
  specifications were wrong (admitting the most negative power of two); all
  were caught by failed proofs before any claim about Go was made.
* Model fidelity is backed by 47,640 differential vectors (`math/bits`) and
  16,128 slice configurations (`slices.Insert/Delete/Replace` with every
  aliasing pattern of a 5-element array) computed by the real toolchain and
  re-evaluated by the Lean models with zero mismatches, plus Go property
  tests with `math/big` as oracle.
* The aliasing-aware slice model agrees with the documented specification on
  531,531 configurations (bounded exhaustive search, N ≤ 10), including
  offsets and capacities of `s` that Go's own `TestInsertOverlap` and
  `TestReplaceOverlap` do not vary.
* A translator from `generic.rules` to Lean generates and proves 74
  constant-folding theorems (kernel-only) and lists the 60 constant rules it
  does not cover.

## 2. What was built

See `README.md` (layout) and `docs/architecture.md` (pipeline and trusted
base). Deliverables by mission phase:

| Phase | Deliverable | Where |
|---|---|---|
| 0 prior art | comparison matrix, 7 questions, build-vs-reuse | `docs/prior-art.md` |
| 1 boundary | pinned versions, assumptions A1–A6, feature table | `docs/semantic-boundary.md` |
| 2 prototype | `lake build`, `lake exe audit`, `lake exe checkvectors`, Go tests, `scripts/check.sh`, CI, flake | repo root |
| 3 targets | 42-entry manifest with status history | `targets/properties.yaml` |
| 4 pipeline | acquisition (checksums, generated tables), models, specs, proofs, counterexample → Go reproducer | `GoInLean/`, `scripts/mutation_test.py` |
| 5 validation | differential vectors, exhaustive 8/16-bit Go checks, `math/big` oracles, fuzz target, mutation test, negative controls, finding directory | `go/tests`, `mutants/`, `findings/BITS-ADD-64-NOPRE` |
| 6 compiler | 12 rule families modelled and proved, 1 historical rule refuted; 74 constant-folding rules translated and proved by `scripts/rules_to_lean.py` | `GoInLean/Compiler/`, `docs/compiler-verification-feasibility.md` |

## 3. Results by property

Full details (source lines, oracle, trust tier, history) are in
`targets/properties.yaml`; `python3 scripts/validate_manifest.py` checks it
against the audited Lean environment.

### 3.1 Proved in the model (38)

| Id | Function(s) | Statement | Trust |
|---|---|---|---|
| BITS-LEN-8/16/32/64 | `Len8..64` | = bit length (oracle `BitSpec.len`) | bv_decide |
| BITS-LZ-64 | `LeadingZeros8..64` | = width − bit length | bv_decide |
| BITS-TZ-8/16/32/64 | `TrailingZeros8..64` | de Bruijn tables/constants give the lowest set bit | bv_decide |
| BITS-POP-8/16/32/64 | `OnesCount8..64` | table and SWAR algorithms = popcount | bv_decide |
| BITS-ROTL-8-16-32, BITS-ROTL-64 | `RotateLeft8..64` | = `BitVec.rotateLeft (k mod w)`; negative k rotates right | bv_decide |
| BITS-REVB-16-32-64 | `ReverseBytes16..64` | = byte reversal | bv_decide |
| BITS-REV-8-16-32-64 | `Reverse8..64` | = bit reversal | bv_decide |
| BITS-ADD-32/64, BITS-SUB-32/64 | `Add32/64`, `Sub32/64` | 2w-bit identities under carry/borrow ∈ {0,1}; carry/borrow out ≤ 1 | bv_decide |
| BITS-MUL-32 | `Mul32` | hi ++ lo = 64-bit product | kernel |
| BITS-MULHI-8 | `Mul64` high-half algorithm at half-width 4 | = high half of the product | bv_decide |
| BITS-DIV-PANIC | `divGeneric` (every half-width) | panics exactly as documented | kernel |
| BITS-DIV-8-FASTPATH, BITS-DIV-8 | `Div64` algorithm at width 8 | = exact quotient/remainder when no panic | bv_decide |
| SORT-SEARCH-MID | `int(uint(i+j)>>1)` | exact midpoint, no overflow, `i ≤ h < j` | bv_decide |
| SORT-SEARCH-SPEC | `sort.Search` | smallest true index or n (monotone f) | kernel |
| SLICES-COMPACT-NOADJ | `slices.Compact` (list model) | no adjacent duplicates, sublist, head kept, length ≤ | kernel |
| SLICES-INDEX-CONTAINS | `slices.Index/Contains` (list model) | first occurrence / membership | kernel |
| RULE-POW2-STRENGTH-8, RULE-POW2-STRENGTH-32-64 | `Mul/Divu/Modu` by 2^k, signed non-negative variants | lhs = rhs | bv_decide |
| RULE-SDIV-POW2 | signed `Div` by 2^k, 4-op sequence | lhs = rhs for admissible k | bv_decide |
| RULE-DIV-SPECIAL | `Div` by MinInt, by negative constant | lhs = rhs | bv_decide |
| RULE-SHIFT-ALGEBRA | shift composition/masking | lhs = rhs | bv_decide |
| RULE-BCE | bounds-check facts | index < bound | bv_decide |
| RULE-FOLD-RSHU-AUXINT | constant folding of `Rsh8Ux64` | value and AuxInt canonical form | kernel |
| RULE-CONST-FOLDS | 74 generated constant-folding rules | Go typed-AuxInt expression = `OpSem` | kernel |

### 3.2 Refuted in the model (model counterexamples)

| Id | Statement | Witness | Classification |
|---|---|---|---|
| BITS-ADD-64-NOPRE | Add64 identity *without* the carry ∈ {0,1} precondition | x = y = MaxUint64, carry = 2 | `known_issue` (#54255, documented precondition) — see `findings/BITS-ADD-64-NOPRE/` |
| SORT-SEARCH-MID-NAIVE | naive `(i+j)/2` = Go's midpoint | i = 1, j = MaxInt | `counterexample_in_model` (hypothetical code, Go avoids it) |
| RULE-FOLD-RSHU-GO16 | Go ≤ 1.6 constant-folding rule keeps AuxInt canonical | c = −3 (253), d = 0 | `known_issue` (#15175, fixed Go 1.7) |
| (RULE-SDIV-POW2 history) | 4-op sequence for k = w−1 | n = MinInt | specification error on our side; rule's side condition excludes it |

### 3.3 Model mismatches found by proofs (4, all fixed)

`TrailingZeros16/32/64`, `OnesCount64`, `Reverse32/64`: the first Lean
transliteration used Lean's operator precedence for `x>>1&m + x&m` and
`(x&-x)*c>>27`; Go parses `* / % << >> & &^` at one level. `bv_decide`
returned concrete inputs (e.g. `x = 2#16`, `x = 2^31`, `x = 2^64−1`) that
disagreed with Go. Lesson recorded as assumption A6 and as a rule for
transliteration; the differential vector check would also have caught it.

### 3.4 Inconclusive (5, plus one partial)

| Id | Blocker |
|---|---|
| SLICES-INSERT-ALIAS, SLICES-DELETE-CLEAR, SLICES-REPLACE-ALIAS | no general proof over the heap model; evidence: `lake exe slicesearch 10` (531,531 configurations, 0 mismatches vs spec) and `lake exe checkslices` (16,128 configurations replayed through real Go, 0 differences in contents and backing array) |
| BITS-MUL-64 | SAT encoding of 16/32/64-bit general multiplication times out (h = 8 after 400 s); only the half-width-4 instance of the same algorithm and the `lo` half are proved |
| BITS-DIV-64 | 128-bit division out of SAT reach; the identical algorithm (fuel-8 loops included) is proved at width 8 in ≈ 80 s with a 20M-heartbeat budget |
| (RULE-POW2-STRENGTH-32-64, partial) | 64-bit *symbolic*-divisor `Div64u/Mod64u` time out; constant-divisor instances proved; 32-bit symbolic proved |

None of these is a counterexample. All are covered by differential vectors
and `math/big`-oracle Go tests (boundary values + fuzz target).

### 3.5 Go discrepancies reproduced

| Finding | Status |
|---|---|
| `bits.Add64(MaxUint64, MaxUint64, 2)`: pure-Go formula gives (0, 1), arm64 intrinsic gives (MaxUint64, 1), mathematics says (0, 2) | out of contract; `known_issue` #54255; recorded in `findings/BITS-ADD-64-NOPRE/` with reproducer, source and validation JSON; **no upstream action** |

No potentially novel issue requiring human review was produced.

### 3.6 Independent review

An adversarial reviewer agent, started with a fresh context and instructed
to falsify the `math/bits` model (`review/bits-model-review.md`), found no
mismatch: every function was re-parsed against Go's precedence rules, the
four deliberate deviations in `Div64` (`clzW` oracle, fuel-8 loops, bare
`/` on provably non-zero divisors, out-of-range `tab`) were argued or
measured unobservable (instrumented Go copy: the correction loop never runs
more than twice over 40M triples), and 9,051,590 differential vectors
between a pure-Go copy of `bits.go` (compiled without intrinsics) and the
Lean model agreed, as did panic kinds and order. The reviewer's
specification findings (no theorems for `Rem64`'s "never panics on
quotient overflow", for `Div32`/`Rem32`, no `_neg` rotate theorem at widths
8/16/32; the "execution time does not depend on the inputs" clauses are
outside the model) are recorded as the first items of future work; drafts
of the `Rem`/`Div32` theorems exist but did not yet build inside the
library when the session's budget ran out.

### 3.7 Iteration 2 additions

* **`Mul64` at 64 bits proved** (kernel only, < 1 s): every intermediate
  64-bit operation of the schoolbook algorithm is shown not to wrap, the
  schoolbook identity is closed by `grind`, the final step by `omega` over
  product atoms (`GoInLean/Properties/Mul64.lean`).
* **ARM64 shift lowering** (`ARM64.rules:145-200`): all 96 instances of the
  `Lsh/Rsh/RshU (8|16|32|64)x(8|16|32|64)` rules, bounded and unbounded, are
  generated by `scripts/arm64_shift_rules.py` and proved with a machine model
  in which the bits of a register above the Go type's width are arbitrary and
  `LSLV/LSRV/ASRV` use the amount modulo 64. A mutant comparing the raw 32-bit
  amount register (the bug class of golang/go#79886, fixed in Go 1.27) is
  refuted with `ry = 0x1_0000_0017`. On the binary side,
  `go/tests/shifts_gen_test.go` runs all 48 shift kinds with dirty high
  register bits on darwin/arm64 (assembly inspected: `LSL` uses the raw
  register, `MOVWU` precedes `CMP $64`): no discrepancy.
* **AMD64 shift lowering** (`AMD64.rules:194-224`): the same 96 rule
  instances, with an x86 model where 8/16/32-bit shifts mask the count to
  5 bits, 32-bit operations zero the upper half, and saturation uses
  `SBB…carrymask`/`NOT`/`OR`. All proved; a mutant using a 64-bit compare on
  an 8-bit amount is refuted (`ry = 2^63`). The generated execution tests pass
  as amd64 binaries (run under Rosetta 2), whose assembly matches the
  modelled sequence.
* **Rotate lowering** (ARM64 and AMD64, incl. `ROL x (NEG y) => ROR x y`
  and constant-count folding) proved with the same register model; a mutant
  omitting `ZeroExt8to64` before `SRL` is refuted.
* **Reviewer gaps closed**: `Rem64` never panics on quotient overflow (every
  half-width), `Rem` exact at width 8 even when `hi ≥ y`, `Rem32` exact,
  `Div32` returns the exact quotient/remainder (Nat-level proofs).
* **Length-overflow guards**: `Repeat` (strings, bytes, slices) and
  `slices.Concat` guards are proved *exact*; `Join`'s separator guard is
  proved *sound* but shown *not exact*, and the inexactness is reproduced in
  Go with `unsafe.String` (`findings/JOIN-GUARD-CONSERVATIVE`). It is the
  only Go-side discrepancy found by the project; it is unreachable without
  `unsafe`, its alternative is a fatal out-of-memory, and it is recommended
  *not* to be reported.

## 4. Success criteria check

| # | Criterion | Status |
|---|---|---|
| 1 | prior art + boundary documented | yes (`docs/prior-art.md`, `docs/semantic-boundary.md`) |
| 2 | reproducible build | yes: pinned Lean 4.35.0 (no deps) and Go 1.25.5; `scripts/check.sh`; CI workflow; Nix dev shell (elan + Go; not exercised in CI) |
| 3 | non-trivial Go semantics modelled and validated | fixed-width integers + all of `math/bits`; validated by `decide` tables, 47,640 vectors, Go tests |
| 4 | meaningful properties registered | 42 |
| 5 | several non-trivial properties proved | 37, including de Bruijn ctz, SWAR popcount, carry/borrow formulas, Knuth division at width 8, compiler rule soundness |
| 6 | deliberately incorrect implementations detected | 5 mutants refuted and reproduced (`scripts/mutation_test.py`) |
| 7 | genuine model-level counterexample reproduced against its reference | BITS-ADD-64-NOPRE reproduced against both the pure-Go formula and the compiled intrinsic |
| 8 | every result distinguishable from a confirmed Go defect | manifest statuses + validator; no entry claims `go_discrepancy_reproduced` as a defect |
| 9 | CI checks proofs and Go tests | `.github/workflows/ci.yml` runs `scripts/check.sh` |
| 10 | reproducible without the AI agent | all steps are scripts; no AI service is called anywhere |

## 5. Limitations

1. **Model ≠ binary.** `proved_in_model` is about the transliterated portable
   Go code. The compiler intrinsifies most `math/bits` functions on
   amd64/arm64; the intrinsic is only exercised by tests (A4). The
   `Add64`/carry = 2 case shows the two can differ (out of contract).
2. **Trusted base.** 67 theorems depend on `bv_decide`'s native LRAT check
   (Lean compiler in the trusted base). julia-in-lean avoids this; we accept
   it for 64-bit bit tricks and report the tier per theorem.
3. **SAT limits.** General multiplication beyond 8×8 bits and 64-bit
   division with symbolic divisors are out of reach of bit-blasting;
   algebraic proofs over `Nat` are needed (future work).
4. **Slices.** The list model has no capacity or aliasing. The
   backing-array model (`Semantics/Slice.lean`) does, and the historically
   buggy `slices.Insert/Replace` (#60138) are now stated and checked
   exhaustively on bounded domains, but not proved in general; capacity
   growth is simplified to the minimum (Go rounds to size classes).
5. **Compiler rules** are checked as equations, outside the matcher, rule
   ordering, fact propagation and panic edges; `isNonNegative` is assumed,
   not derived. Architecture-specific lowering rules, where recent
   miscompiles cluster, are not modelled.
6. **Review depth.** One independent reviewer agent run covered `math/bits`
   only; the slices and compiler models have not been reviewed
   independently.
7. **Coverage of ambiguity.** Only two documentation ambiguities were
   exercised (carry ∈ {0,1}; `Mod64u` after a trapped division). The
   `strings`/`bytes` packages were surveyed but not modelled.

## 6. Recommendations (prioritised)

1. **General proofs over the backing-array slice model** (induction on the
   heap model, or a symbolic-execution tactic) for `Insert`, `Replace`,
   `Delete`, so that the bounded exhaustive evidence becomes
   `proved_in_model`; then extend the enumeration to `Concat`, `Grow`,
   `Repeat` and to pdqsort's non-strict-weak-order behaviour (#52518).
2. **Algebraic (Nat-level) proofs** for `Mul64` and `Div64` using
   `BitVec.toNat` lemmas, so the 64-bit theorems leave `inconclusive`.
3. **Extend the rule translator** beyond constant folding to the
   shift/power-of-two/mask rules with one variable operand (pattern
   variables become universally quantified `BitVec`s, `uses == 1` and
   `config.*` conditions excluded); then ARM64/RISCV64 shift lowering rules
   with exact machine masking semantics (`docs/compiler-verification-feasibility.md`).
4. **Independent reviewer agent** that receives model + Go source and must
   either produce a differential-vector disagreement or sign off, before a
   property may be marked `proved_in_model`.
5. **`strings.Repeat`/`bytes.Repeat`/`slices.Repeat` overflow guard** via
   `bits.Mul`, as a Nat-level theorem (regression oracle #16237).
6. **Intrinsic coverage**: generate vectors with `GOAMD64`/`GOARCH` variants
   and with `-gcflags=-d=ssa/intrinsics/off` (if available) to separate
   intrinsic from portable behaviour explicitly.

## 7. Commands and versions

```sh
# versions
lean --version      # Lean (version 4.35.0, ...)
go version          # go1.25.5
# everything
scripts/check.sh
# pieces
lake build
lake exe audit                                   # 187 theorems: 120 kernel-only, 67 bv_decide
lake exe slicesearch 10                          # bounded exhaustive slices model vs spec
( cd go && go run ./tests/vectors_slices 5 ) > build/slices_vectors.json && lake exe checkslices build/slices_vectors.json
python3 scripts/rules_to_lean.py --check         # generated constant-folding theorems up to date
( cd go && go test ./... )                        # property tests
( cd go && go run ./tests/vectors ) > build/bits_vectors.json && lake exe checkvectors build/bits_vectors.json
python3 scripts/validate_manifest.py targets/properties.yaml build/audit.json
python3 scripts/mutation_test.py
( cd go && go test ./tests -run=NONE -fuzz=FuzzAddSubMulDiv -fuzztime=30s )
```

Go source checksums and the Lean toolchain are listed in
`docs/semantic-boundary.md`.
