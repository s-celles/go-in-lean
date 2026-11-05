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
* **Two new Go compiler bugs were found and reproduced**: golang/go#82763 (§3.8, reported) and golang/go#82767, a master-only regression (§3.9), both reported; no defect was found in the standard-library functions studied, which behave as documented
  in go1.25.5.
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

### 3.8 A compiler miscompilation found by the generated-rule triage

`scripts/generic_rules_to_lean.py` translates 830 instances of `generic.rules` into Lean and
bit-blasts each one; failures are triaged automatically (`targets/generic_rules_triage.json`):
786 proved, 29 timeouts, 7 spurious, **8 counterexamples**, all in the `c < e` branch of the
`((x >> c) & d) << e` rules. The rules compare the int64 AuxInts of the two constant shift
counts with signed `c >= e` / `c < e`, while Go shift counts are unsigned; a count `c >= 2^63`
takes the wrong branch. Reproduced on the real compiler (go1.25.5, go1.26.10, go1.27.3 and
master `babb75be`, arm64 and amd64): `((x >> (1<<63)) & 3) << 1` is 0 for `x = -1` instead
of 6; the variable-count version is correct; the SSA dump shows the rule firing in `opt`; the
same wrong value appears when the constant arrives through inlining. Unsigned operands are
protected by an earlier fold. Adding `c >= 0 && e >= 0` is proved sufficient for all 16
instances in Lean and, applied to master, fixes the reproducer while the compiler's own tests
still pass. After human review it was reported as
[golang/go#82763](https://github.com/golang/go/issues/82763)
(`findings/SSA-SHIFTMASK-SIGNED-COUNT/`). Severity: low–medium (silent wrong code for a
pathological but legal constant count).

Lesson for the pipeline: `lake env lean` once crashed on an internal panic
(`Nat.shiftl exponent is too big`) while evaluating a shift by 2^63, and a filtered command
output made the crash look like success. The triage scripts now fail on any Lean exit without
a parsed error, and every generated file is also built by `lake build` in CI.

### 3.9 Iteration 4: magic division, signed-count scan, metamorphic fuzzing, knownbits

* **Magic-constant division** (`scripts/magic_rules_to_lean.py`): the `umagic`/`smagic`
  rules instantiated on all 8-bit divisors and sampled 16/32/64-bit ones; 644 instances
  proved, 0 counterexamples (timeouts excluded, recorded in the triage file).
* **Signed-count lint** (`scripts/scan_signed_counts.py`): 48 rules on master treat a constant
  shift count as signed; all but two families only become more conservative. The rotate
  recognition rules (generic.rules:2220-2223) are wrong for a count ≥ 2^63 but unreachable
  (refuted in `LatentRotate.lean`, correct results on go1.27.3 and master).
* **Metamorphic fuzzing** (`scripts/metamorphic_fuzz.py`, `scripts/fuzz_campaign.sh`): each
  random integer expression is compiled with its constants inline, passed at run time, and
  through an inlined helper; a canary with the golang/go#82763 pattern checks sensitivity.
  200 seeds on go1.27.3: 0 mismatches. 200 seeds on master: 7 failing seeds, all explained by
  a **master-only regression** (`findings/SSA-COMPOSE-CONST64-TYPE`): the 8/16/32-bit
  shift-composition rules type the combined count with the shifted value's type (the class of
  golang/go#81868, whose fix did not touch these rules), and master's `InitLimit` now
  truncates that constant to the type width, so `prove` marks the shift bounded.
  `(int32(2) >> 1) >> (1<<62)` gives 1 instead of 0; a one-type fix in nine rules is
  validated on master. Reported as golang/go#82767 after human review.
* **`knownbits`** (new pass on master): every fold case, both simplifications and all 48 shift
  ops at all widths are proved sound against Go semantics (`KnownBits.lean`); a variant
  without the bounded hypothesis is refuted, so the theorems are not vacuous.
* **`prove` interval arithmetic** (master): `Limit.Add/Sub/Com/Neg/Mul/Bitlen/Ctz/Popcount`
  and `PropagateUnsignedSignedRelationship` proved sound at all widths (Mul at 8/16 bits) under
  the hypothesis that operand limits are normalised to the value width; `com32_needs_norm`
  shows the hypothesis is necessary, and the only way to violate it is a `Const64` typed
  narrower than 64 bits, i.e. the root cause of golang/go#82767.
* **golang/go#82767 is less exotic than first reported**: for int8 the combined count is
  truncated to 8 bits, so `(y >> 128) >> 128` already misbehaves on master (100 instead of 0);
  a second campaign (200 seeds, master, amd64) found 8 failing seeds, all fixed by the patch.

### 3.10 Iteration 5: what changed on master, and a type-consistency lint

* **New rules on master** (`scripts/rules_diff.py`, `scripts/check_new_rules.py`): a
  normalised diff of the rule files between go1.27.3 and master `babb75be` gives 241
  new or modified generic rules (and a large refactor of the architecture and SIMD files).
  95 new generic rule instances fall in the translatable fragment: 89 proved, 6 SAT
  timeouts, 0 counterexamples. The rest are memory rules (Load/Store/Move/Zero, 111 with
  symbolic aux) and 128-bit tuple ops.
* **Type-consistency lint** (`scripts/rules_type_lint.py`): flags right-hand-side nodes
  whose annotated type width differs from the op width (the class of golang/go#81868 and
  golang/go#82767). It reports 74 annotations on go1.25.5, 45 on go1.27.3 and master: the
  29 fixed by CL 795240 disappear, and on master it finds exactly the nine
  shift-composition rules of golang/go#82767 plus deliberate "type punning" (lowering rules,
  divmod expansions whose values fit, rules for 32-bit targets). No new instance.

### 3.11 Iteration 6: other architectures under emulation

* **Cross-architecture fuzzing** (`scripts/cross_campaigns.sh`): the metamorphic fuzzer
  (`go run -exec qemu-<arch>`) on 386, arm, mipsle, riscv64, ppc64le, ppc64, s390x, loong64 and
  mips64le, with go1.27.3 and master; a per-architecture canary (golang/go#82763) is detected on
  all nine. 2,160 seeds per run (60 per configuration).
* **Fuzzer defect found and fixed.** The program generator dropped ill-typed expressions in at
  most 30 rounds of ten compiler errors, then silently kept a program that did not compile; the
  campaign script counted a run without output as a pass. All `--branchy` and `--index` seeds of
  the earlier amd64 campaigns were in that state (the plain campaigns were not affected and are
  the only ones reported in §3.9). Fixed: `go build -gcflags=-e` reports every error, the build
  uses the target `GOARCH`, exhaustion is an error, failed runs are reported, and variables are
  rendered with an explicit conversion (half of the branchy expressions were ill-typed).
* **Three architecture-specific miscompilations**, reported after human review as golang/go#82772 (MIPS), #82773 (riscv64) and #82774 (s390x):
  * `findings/MIPS-RSH8-SIGNEXT16`: `MIPS.rules` lowers `Rsh8x(32|16|8)` with `SignExt16to32`
    instead of `SignExt8to32` (since go1.8). `int8(127 * -15) >> 8` gives -8 instead of -1 on
    mips and mipsle; 35 of 60 mipsle seeds failed on go1.27.3, 0 on master with the fix.
  * `findings/RISCV64-SLLI-NARROW-TYPE`: go1.26 regression. A 64-bit `SLLI` created by a lowering
    rule is typed `int8`, and the new `(SLLI <t> [c] (ADD x x))` fold trusts that type:
    `int8(x - (-x)) >> 8` compiles to the constant 0 (spec -1). Same class as golang/go#82767.
  * `findings/S390X-CMPU-SIGNEXT`: the rule narrowing 64-bit compares to 32 bits pairs an
    unsigned compare with a sign-extended byte/half-word; `uint64(int8(-128)) < 0xFFFFFFFF` is
    true. The rule is old; s390x's register ABI (go1.26) made it reachable.
  Each has a Lean model with a kernel-checked counterexample and a proof of the fix, a Go
  reproducer run under qemu, and a fix validated on master (compiler, codegen and fixedbugs
  tests pass). The riscv64 and 386 failures of the first run with a `((x >> c) & d) << e` shape are
  golang/go#82763 (go1.23.12 correct, go1.24.0 wrong).
* **Architecture variants** (`SPECS` in `scripts/cross_campaigns.sh`): GORISCV64=rva22u64/rva23u64,
  GOPPC64=power9/power10, GOARM=5/6, GO386=softfloat, GOMIPS=softfloat, GOARM64=v9.0 and
  GOAMD64=v4 (2,640 seeds). Two more defects, reported after human review as golang/go#82775 (ppc64) and #82776 (MIPS):
  * `findings/PPC64-EXT-SIZE-BYTES`: ppc64 rules eliminating an extension after a 32-bit right
    shift compare `Type.Size()` (bytes) with bit widths, so `int32(int16(x >> 1))` keeps 32 bits
    (go1.21 .. master).
  * `findings/MIPS-CONST64-COUNT-UINT32`: MIPS lowers constant 64-bit shift counts with
    `uint32(c)` (ARM and 386 use `uint64(c)`); a shift merge in `late_opt` after `dec64` creates a
    count ≥ 2^32, so `(x >> 7) >> (uint64(y) | 0xFFFFFFFF)` becomes `x >> 6`.
* **Narrow-argument ABI check**: callers extend narrow integer arguments on all nine
  architectures (computed `int8`/`uint16`/`int32` arguments), so the ppc64/s390x rules that drop
  the extension of an `Arg` are safe in practice; the internal ABI document does not state it.
* **`--bits`** (generator): `math/bits` intrinsics and `min`/`max`, lowered by
  architecture-specific rules (Zbb, power9 `cnttz`, s390x `FLOGR`).
* **`--bits` campaign** (12 targets, 2,400 seeds): one more defect, reported after human review as golang/go#82777:
  `findings/ARM64-CSINV-NOT` (native arm64, go1.21 .. master): a conditional select of `^y`
  whose condition becomes constant during `lower` folds to the boolean `Not`, i.e. `y ^ 1`.
  The master-only index-mode failures on riscv64 (rva23u64) are an instance of the open
  golang/go#80577 (a `REV8` typed `uint16` spilled with 2 bytes); the arm and ppc64le ones are
  not yet analysed.
* **Host notes.** Lean proofs run on the development Mac; on a Linux host with little swap, `bv_decide`
  can fail with "resource exhausted (error code: 12)" because the Lean process reserves more
  virtual memory than RAM plus swap and the solver cannot be spawned. Hand-written `bv_decide`
  calls now carry an explicit 120 s limit (the default 10 s was exceeded on loaded hosts).

### 3.12 Iteration 7: an ARM fold typo, floating point, and a ppc64 instance of #80577

* **`findings/ARM-MVNSHIFTRA-CONST`** (reported as golang/go#82786): `ARM.rules` folds
  `MVNshiftRA (MOVWconst [c]) [d]` to `c >> d`, dropping the complement that its LL/RL siblings keep;
  go1.15 had `^int64(int32(c)>>d)` and the `^` was lost in the go1.16 typed-AuxInt conversion. Through
  the 32-bit `Ctz64` decomposition, `bits.TrailingZeros64(0)` evaluates to 32. One-line fix validated on
  master. A scan of every `<op>shift(LL|RL|RA) (MOVWconst [c]) [d]` fold in ARM.rules finds no other
  inconsistency.
* **Floating point and conversions** (`scripts/float_fuzz.py`, `float_cross.sh`): constants are
  injected as `math.Float64frombits(bits)` so the SSA backend folds them on the host with IEEE
  semantics (Go constant expressions are exact and would differ legitimately); every arithmetic result
  is wrapped in an explicit conversion (no FMA fusion); float->int conversions are range-guarded; NaNs
  are canonicalised. Disassembly confirms the constant versions are folded at compile time. 16 targets
  (incl. `GOARM=5`, `GO386=softfloat`, `GOMIPS=softfloat`, power10, rva23) x go1.27.3 and master x 30
  seeds: **no mismatch**, every canary detected. Conversions (incl. int64->float32 double-rounding
  candidates and uint64 on 32-bit ports) and the math intrinsics are consistent on these vectors.
* **`findings/PPC64-SPILL-SIGNEXT-80577`** (known issue): on ppc64, `int16(uint16(int8 y))` keeps type
  `uint16` but holds a sign-extended register; the signed compare's `MOVHreg` is elided, and when the
  value is spilled across a call regalloc restores it with `MOVHZ` (zero-extend) chosen from the type.
  An instance of the open golang/go#80577 not covered by its riscv64 fix. Whether a program hits it
  depends on scheduling, down to source line layout (the scheduler breaks ties by position).

### 3.13 Iteration 8: a sibling-consistency lint, late constants, and a prove soundness bug

* **Sibling-consistency lint** (`scripts/rules_sibling_lint.py`): flags a rule that disagrees with its
  shift-kind (LL/RL/RA) or width siblings, a 64-bit constant count tested through a 32-bit cast, and
  `Size()` (bytes) compared with bit widths. On master it reports exactly the three defects already
  reported (golang/go#82786, #82776, #82775) and nothing else: no other instance of those classes.
* **Late constants** (`metamorphic_fuzz.py --late`): the constants of the const version are loads
  from a read-only string recombined with shifts and ORs, so they fold during lowering and exercise
  the architecture-specific folding rules. Campaign: 15 targets x {--late, --late --bits} x go1.27.3
  and a master carrying all ten earlier fixes (so master failures are new). Every go1.27.3 failure
  disappears with all fixes (known bugs); the riscv64 rva23 index failures are the known golang/go#80577
  instance (REV8 spilled with 2 bytes).
* **`findings/PROVE-EXT-CONST-TRUNC`** (not yet reported; all architectures): prove carries a fact
  `ext(x) op c` over to the narrow `x` with the same constant, and the "x+delta > w" step then truncates
  `c` to `x`'s width. `if int32(int16(x)-513) < -536870911 { sink = 1 }` runs for x = 0 on go1.26.6+,
  go1.27.3 and master (amd64, arm64, arm); a return-form variant is wrong from go1.24.13. The code is
  unchanged since go1.24; go1.26.6's "fix time traveling proofs" backport made the reproducer reach it.
  Fix: carry the fact only when the constant fits (prove, loopbce, checkbce, codegen and fixedbugs pass).

### 3.14 Iteration 9: prove-limit boundaries and differential SROA testing

* **`prove`/`Limit` boundary synthesis** (`scripts/prove_limit_fuzz.py`): 330 isolated
  two- and three-stage shift compositions around the sign bit and modulus of `int8`, `int16`
  and `int32`. A pristine `672197524bb0` produces 60 ICEs, all the already identified #82767
  mistyped-count root reaching `flowLimit`; the same commit with CL 857342 patchset 1 is
  330/330 clean. Current master `ede4e4ff00` still has the original rules and the same 60/330
  ICE result. Left shifts and unsigned right shifts are clean controls. The audit found no
  distinct panic edge in the other host shifts/divisions in `prove.go`.
* **`decomposeAddr` differential harness** (`scripts/decompose_addr_fuzz.py`,
  `scripts/decompose_addr_campaign.py`): aggregate-heavy programs are compiled and executed
  with the new SROA pass enabled and with `-d=ssa/decompose_addr/off`. The generator covers
  nested structs and arrays, partial zero/move operations, strings, slices, interfaces,
  complex values, pointer-containing aggregates live across `runtime.GC`, and deterministic
  differently-shaped moves through `unsafe.Pointer`. On tip `672197524bb0`, 1,200 seeds
  (about 88,000 generated functions) are clean across amd64/v3, arm64, arm, ppc64,
  ppc64le, s390x and riscv64; the six non-native targets run under QEMU. A first unsafe
  probe that read padding produced a reproducible harness-only divergence and was discarded;
  the retained oracle initializes and observes only specified bytes.
* **Spill/restore boundary synthesis** (`scripts/spill_restore_fuzz.py`): a stable two-function
  reproducer replaces the earlier schedule-sensitive ppc64 #80577 case. Merely keeping
  `int16(uint16(int8(-1)))` live across a call is sufficient: arm64, ppc64le and ppc64 restore
  it unsigned before a signed comparison and return `999` instead of `-1001`. PPC64 also fails
  for the 16→32 analogue. The defect is present from at least go1.21.13 through go1.27.3 and
  current master; 386, arm, mipsle, mips64le, riscv64, s390x and loong64 are clean controls.
  This broadens the known #80577 architecture/width extent without introducing a new root cause.
* **Spill/restore producer audit** (2026-11-05): the harness now crosses every widening pair with
  sign/zero extension directions, argument/load/call/shift/multiply/Phi/rotate/reverse-byte
  producers and pressure 0–20. Pristine tip has 105/945 signed-chain mismatches on arm64 and
  441/945 on ppc64le; every failing producer/width group fails at all 21 pressures. Seven other
  architectures are clean at pressure zero, as is the symmetric zero-extension direction on
  arm64 and both PPC64 endiannesses. The same spill/restore contract explains every mismatch,
  including the new `ReverseBytes16` route. Local ARM64 and PPC64 guards make all 945 cases clean
  on arm64 and ppc64le (and 45/45 at pressure zero on big-endian ppc64). CL 825904 PS6 defines
  central restore predicates but does not yet apply them to these double/repeated-extension rules.

### 3.15 Iteration 10: alternative Go implementations as a differential control

`scripts/alt_compiler_diff.py` (2026-11-05) runs the same deterministic programs through
independent Go implementations and compares exit code, stdout and stderr with gc, and the
expression lines with the Lean oracle (`lake exe oracle`). gc is the *practical* reference
only: a toolchain that disagrees with gc is classified, not convicted, and the majority
never decides - a gc result that contradicts the oracle is a lead even when every other
implementation agrees with gc. Hike (`kanryu/hike-lang`) is a Go-inspired language, not a
Go implementation, and is not used as an oracle.

**Toolchains (GEEKR9, NixOS 26.05, x86-64, 16 cores).**

| Name | Implementation | Version | Build / run |
|---|---|---|---|
| `gc` (reference) | gc | go1.27.3 (nixpkgs `go_1_27`) | `go build -o prog main.go`, `GO111MODULE=off GOTOOLCHAIN=local CGO_ENABLED=0` |
| `gc-noopt` | gc | go1.27.3 | `go build -gcflags='all=-N -l'` |
| `gc-1.26` | gc | go1.26.10 (nixpkgs `go`) | as `gc` |
| `gc-tip` | gc | go1.28-devel_56ae71df05 (2026-11-03) | as `gc` |
| `gccgo-O0`, `gccgo-O2` | GCC Go frontend | gccgo (GCC) 16.2.0 | `gccgo -O0`/`-O2 -o prog main.go` |
| `tinygo` | TinyGo (LLVM) | 0.43.0, using go1.27.3 and LLVM 22.1.8 | `tinygo build -o prog main.go` (default `-opt=z`) |
| `llgo` | LLGo (LLVM) | `xgo-dev/llgo` commit `d4b248e8c779` (v1.0.9-144), go1.27.3, LLVM/Clang/LLD 22.1.8 | `llgo build -o prog main.go` |
| `yaegi` | Yaegi (interpreter) | 0.16.1 | `yaegi run main.go` |

**Compatibility matrix** (the portable subset as generated; ✓ = builds and agrees with the
oracle on every expression line of the smoke and campaign runs).

| Feature | gc | gccgo -O0/-O2 | TinyGo | LLGo | Yaegi |
|---|---|---|---|---|---|
| int/uint 8-64 arithmetic, bitwise, `&^`, comparisons | ✓ | ✓ | ✓ | ✓ | ✓ |
| conversions and truncations | ✓ | ✓ | ✓ | ✓ | ✓ |
| constant, variable, signed (masked) and >= 2^63 shift counts | ✓ (tip: #82767) | ✓ | ✓ | ✓ | ✗ in assignments with a compound count (below) |
| if/else Phi, bounded loops, `//go:noinline` | ✓ | ✓ | ✓ | ✓ | ✓ (pragma ignored) |
| `math/bits` (separate `bits` suite) | ✓ | ✓ | ✓ | ✓ | ✓ apart from the same shift bug |
| guarded `/`, `%`, including `MinInt / -1` | ✓ | ✓ | ✓ | ✓ | ✓ |

**Results.** Generated programs carry 10 oracle-checked functions and 2 bounded-loop
functions over 6 input pairs (72 expression lines checked against the Lean oracle, 12 loop
lines against gc only); inputs are passed either as literals or through a run-time-filled
array, and selects are lowered either to if/else or to the canary's default-then-override
shape.

| Run | Programs | Wall time (16 jobs) | Non-clean results |
|---|---|---|---|
| smoke, `core` + `bits`, seed 1 | 16 + 16 | 38 s + 25 s | none (288 executions, all agree with the oracle) |
| `core`, seed 20261105 | 1,500 | 41.6 min | yaegi: 8 `output_mismatch`, 1 `run_error`; gc-tip: 1 `output_mismatch` |
| `bits`, seed 20261105 | 500 | 9.7 min | yaegi: 6 `output_mismatch` |
| `core` rerun, same seed, first 300 | 300 | 5.8 min | identical sources and statuses on all 300 cases (`--compare-with`) |
| `directed` | 27 | 39 s | the known gc bugs only (below) |

Across the 2,000 campaign programs (18,000 builds and runs), gc go1.27.3, gc `-N -l`,
go1.26.10, gccgo -O0/-O2, TinyGo and LLGo are clean and agree with the oracle on every
expression line; there are no `build_error`, `timeout` or `unsupported` results, and no
gc reference failure (the generator emitted no invalid program).

The `directed` suite reproduces the tracked amd64-relevant gc bugs and shows the
alternatives as an independent majority that agrees with the specification: on the
#82763, #82825 and #82839 canaries gc go1.27.3 disagrees with the oracle and gccgo
(both levels), TinyGo, LLGo and Yaegi all agree with it; the self-checking regression tests
`findings/*/cl/issue82763.go`, `issue82825.go` and `issue82839.go` fail under gc and pass
under all five alternatives. The version profile matches `docs/upstream-status.md`:
#82825 is fixed on tip, #82839 is present from go1.26 through tip, #82763 on every gc,
and the tip-only #82767 shows up on tip as a canary mismatch, a failing self-check and an
ICE on the `package main` form of `ice_reproducer.go`. The canaries for other
architectures (mips, ppc64, riscv64, s390x, arm, arm64, power10) are clean on amd64 for
every implementation, as expected, and so is the #80577 spill reproducer (an arm64/ppc64
defect).

**Triage of the divergences.**

| Divergence | Classification | Evidence |
|---|---|---|
| gc-tip, `core-20261105-00565`: `(int16(x) >> 1) >> 2^32` gives `x >> 1` (`1924` instead of `-3` after `^t1 +`) | likely gc bug, **already known**: golang/go#82767 (tip-only shift-composition count typed with the shifted value's type) | spec and oracle give 0; go1.27.3, go1.26.10 and the five alternatives agree; reduced to `func f(x int16) int16 { return (x >> 1) >> uint64(1<<32) }`, which gives 1927 on tip (int8: 42, int32: 1927, also with count 2^62) and 0 on go1.27.3. CL 857342 is still unmerged on this tip (`56ae71df05`). An organic rediscovery, not a new finding |
| yaegi, 14 `output_mismatch` (8 `core` + 6 `bits`) | bug of the alternative toolchain (Yaegi 0.16.1) | an assignment `v = x >> (count expr)` converts the count to the operand type (`uint32(2^32+1) = 1`); all 14 cases become correct when every such assignment is rewritten as `{ tmp := expr; v = tmp }` (`triage_yaegi.py`); reduced reproducer in `upstream-bugs.md` |
| yaegi, 1 `run_error` (`core-20261105-00481`) | bug of the alternative toolchain, same family | valid Go `r = s >> ((k - k) ^ k)` is rejected while loading ("mismatched types int16 and uint64"); gc and gccgo accept it |

No divergence is attributed to a library or runtime difference, to a program outside the
common subset, to unspecified behaviour, or to the harness. During development, the harness
problems found were fixed before the campaign: a loop variable left unused when the loop
body did not reference `x` (a gc build error in 29/40 smoke programs), and resolving
`/snap/bin/go` through its symlink, which broke the snap's argv[0] dispatch. The Yaegi
defect reproduces on 0.16.3 (released the same day, equal to master) and was reported as
[traefik/yaegi#1750](https://github.com/traefik/yaegi/issues/1750) after a duplicate search
(`upstream-bugs.md`). gccgo, TinyGo and LLGo produced no divergence, so nothing was
reported to them.

**Limits of the multi-implementation oracle.** (1) The alternative implementations share
front ends with gc: TinyGo and LLGo type-check with `go/types` and compile the gc standard
library (from go1.27.3), so a front-end or library defect common to them is invisible; gccgo
and Yaegi are the only fully independent front ends, and Yaegi is the weakest
implementation of the set. (2) The common subset is small by construction (no panics, no
scheduler, no GC, no maps, no formatting beyond `%d`): an alternative toolchain cannot
corroborate a gc bug outside it. (3) The SSA-rule bugs that go-in-lean finds are mostly
architecture-specific lowering; on amd64 the alternatives only see the generic class
(#82763, #82825, #82839 here), so for the other architectures the Lean oracle and the
cross-architecture runs remain the only arbiters. (4) Agreement of five implementations is
not a specification: the oracle is what turns a 1-vs-5 vote into a lead, and the directed
suite shows gc can be the minority *and* wrong. (5) LLGo is a moving target (built from a
daily commit, about 7 s per program), and its result must be pinned to the commit recorded
in `report.json`.

**Reproduction.** Heavy artifacts stay on GEEKR9 under
`~/go-in-lean-runs/alt-compiler/2026-11-05/`: `tools/` (nix GC roots for go, go_1_27,
gccgo, tinygo, yaegi, python3, glibc and gcc runtime libraries; the LLGo checkout, binary
and `llgo-shell` flake; the Lean oracle wrapper; `env.sh`), `runs/` (one directory per
campaign with `report.json` and the kept divergent cases), `campaign.sh`,
`triage_yaegi.py`, and `yaegi-shift/` (the reduced reproducer).

```sh
. ~/go-in-lean-runs/alt-compiler/2026-11-05/tools/env.sh
$ACD list $ACD_TOOLS                               # detection and versions
$ACD run --suite directed --out runs/directed --oracle $ORACLE --jobs 16 $ACD_TOOLS
$ACD run --suite core --seed 20261105 --count 1500 --out runs/core-20261105 \
    --oracle $ORACLE --jobs 16 $ACD_TOOLS
$ACD run --suite bits --seed 20261105 --count 500 --out runs/bits-20261105 \
    --oracle $ORACLE --jobs 16 $ACD_TOOLS
$ACD run --suite core --seed 20261105 --count 300 --out runs/core-20261105-rerun \
    --oracle $ORACLE --compare-with runs/core-20261105/report.json $ACD_TOOLS
python3 -m unittest scripts/test_alt_compiler_diff.py   # harness tests
```

LLGo is built from source in a user directory with
`nix develop tools/llgo-shell` (LLVM 22 stdenv, boehmgc, libffi, openssl, libuv, cjson,
zlib) and `go build ./cmd/llgo`; the `tools/llgo` wrapper sources a cached
`nix print-dev-env` and sets `LLGO_ROOT`, and LLGo binaries run with
`LD_LIBRARY_PATH` pointing at the gcc runtime (`libatomic`, `libstdc++`), which the link
does not record as an rpath. The Lean oracle binary built on the Ubuntu workstation runs on
NixOS through the nix glibc loader.

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
