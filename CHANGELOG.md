# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).
No version has been released yet; everything below is unreleased work since the
first commit (2026-11-01). Upstream issue and CL states are tracked in
`docs/upstream-status.md`.

## [Unreleased]

### Added

- `scripts/ssa_tv.py`: per-pass translation validation of gc's generic SSA with z3. For
  each function it reads the SSA after every pass from `build` up to `lower`
  (`-d=ssa/all/dump`) and checks, for all inputs, that consecutive passes agree on the
  outcome and value, that the facts the IR claims hold (bounded shifts, `[true]` divisions,
  nonzero divisors) and that types match op widths (a narrower type is accepted when z3
  proves the value fits). It finds golang/go#82767, #82873 and #82782 on the affected
  toolchains and nothing on the fixed ones; a sweep of 14,400 generated functions on six
  64-bit targets with go1.27.3 and tip found only #82782, with no false report
  (`docs/research-report.md` 3.18). Tests in `scripts/test_ssa_tv.py` (skipped without
  z3; the cross-check against compiled code needs `go`). README: the approaches table
  gains this tool, constant/opaque twin programs and concolic testing of the standard
  library (both not tested).
- A third form of golang/go#82873 (go1.26 arm64/loong64): `prove` folds
  `bits.Reverse8(y|128) != 255` to true, a silently wrong value
  (`findings/BITREV-INT-SHIFT-COUNT-126/reproducer-wrong-value.go`), posted as a comment.
- Upstream reports: traefik/yaegi#1751 (a negative shift count does not panic) and a
  comment on golang/go#82873 with its `prove` empty-range manifestation (the issue was
  closed shortly before: fixed on master, 1.26 backport declined).

- `--inputs smt` in `scripts/alt_compiler_diff.py` (harness 1.1.0) and
  `scripts/smt_inputs.py`: per-function inputs chosen by z3 on the semantic boundaries
  of each generated expression (shift counts, `MinInt / -1`, comparison edges, select
  arms, truncations, wraparound); the trees are those of the default `pool` mode, which
  is unchanged. Tests in `scripts/test_smt_inputs.py` (skipped without z3), including a
  cross-check of the encoding against gc. README: table of symbolic and concolic
  approaches, implemented or not yet tested.
- `--inputs mixed` (half SMT, half pool inputs per function) and the long-campaign /
  SMT A/B results (`docs/research-report.md` 3.17): on the same programs the SMT selection
  found 42 failing cases and the pool 48 (mixed 37 vs pool 41 on ppc64le/mipsle), a
  difference within noise; the pool remains the default.
- **Long cross-architecture campaign, first round** (2026-11-05, seed 20261110, 12,600
  programs on amd64 and 11 qemu targets): every divergence maps to a known issue. New
  manifestation of golang/go#82873: on go1.26 arm64/loong64 the `int`-typed `BitRev8`
  gives `prove` an empty range and a guarded modulo compiles to an unconditional
  `panicdivide` (`findings/BITREV-INT-SHIFT-COUNT-126/reproducer-prove.go`); confirmed by a
  go1.26 toolchain rebuilt with only the intrinsic result types fixed. Rediscoveries:
  golang/go#82775 (ppc64 16-bit extension elision) and golang/go#82773 (riscv64/loong64).
- `panics` suite in `scripts/alt_compiler_diff.py`: one unguarded division or signed
  shift count per function (never under a select, since the order of two panics is
  unspecified), recovered and reported as the oracle does (`PANIC divideError` /
  `negativeShift`). Its smoke run found that Yaegi does not panic on a negative shift
  count (`upstream-bugs.md`).
- **Cross-architecture alternative-compiler campaigns** (2026-11-05):
  `scripts/alt_compiler_diff.py` gained `--run-prefix`, `--extra-flags`, `--target` and
  `--word-bits`; the same seed ran under qemu on arm64, arm, mipsle, ppc64le, riscv64 and
  s390x with cross gccgo 16.2 and TinyGo. Every architecture-specific canary is
  corroborated by the alternatives; new: golang/go#82873 (go1.26 arm64/loong64 spurious
  `negative shift amount` panic, `findings/BITREV-INT-SHIFT-COUNT-126`), and a backport
  suggestion on golang/go#81842 (ppc64 CR0 clobber, fixed on master only, bisected to
  `6200ca7253`).
- **Alternative Go implementations as a differential control** (2026-11-05):
  `scripts/alt_compiler_diff.py` runs deterministic integer programs through gc,
  gccgo, TinyGo, LLGo and Yaegi, with the Lean oracle as arbiter (`core`, `bits` and
  `directed` suites, per-toolchain statuses, reproducible `report.json`), plus its
  unit tests. A 2,000-program campaign rediscovered golang/go#82767 on tip and found
  a Yaegi shift-count bug, reported as traefik/yaegi#1750 (`upstream-bugs.md`).
- Compiler boundary campaigns: `prove`/`Limit` shift-composition synthesis
  (`scripts/prove_limit_fuzz.py`), `decomposeAddr` SROA differential testing, and a
  spill/restore producer audit across widths, extension directions and register
  pressure (`scripts/spill_restore_fuzz.py`).
- **SIMD specification oracle** (`lake exe oracle-simd`, `scripts/simd_oracle.py`):
  integer and mask chains, then `Float64s`/`Float32s` over executable IEEE 754
  binary64/binary32 models with a fused `fmaBits`, Div/Sqrt, lane reductions,
  saturating and average operations; a SIMD chain fuzzer for `GOEXPERIMENT=simd`.
- A kernel-checked proof that `shiftRound`, the rounding step of the float models,
  is the unique round-to-nearest-even of `m / 2^k`.
- **Lean oracle in the fuzz loop** (`lake exe oracle`, `scripts/oracle_bits.py`) and
  the directed canary suite `scripts/oracle_canaries.py` (13/13 known bugs caught,
  including cross-architecture canaries run under qemu).
- Metamorphic fuzzers: integer (`--bits`, `--late`, `--countvar`, `--carry`,
  branchy and architecture-variant modes) and floating-point/conversion
  (`scripts/float_fuzz.py`); lints for rule type consistency, sibling consistency and
  opcode flag clobbers; master-vs-release rule diff and new-rule checker.
- Lean 4 models and proofs: all of `math/bits`, selected `slices`/`sort`/`strings`
  guards, generated `generic.rules` instances, magic division, ARM64/AMD64 shift and
  rotate lowering, the `knownbits` pass and `prove` interval arithmetic; property
  manifest, axiom audit, differential vectors and mutation testing.
- Findings and Gerrit CL packages for the compiler bugs reported upstream
  (golang/go#82763, #82767, #82772-#82777, #82782, #82786, #82825, #82834, #82839,
  #82847, and the CL 799281 MulAdd gaps), each with a reproducer and a Lean property.
- Visual identity (logo, lockups, brand guide), research map and fuzzing vision.

### Changed

- All written artifacts are in English (2026-11-04).
- The README states the scope of upstream contributions: reports with a reproducer and
  an analysis, no pull request offered by default, and a courteous request to flag any
  mistaken or debatable report.

### Fixed

- The metamorphic fuzzer silently skipped programs that did not compile.
- The `--carry` mode now masks the borrow input to 0 or 1.
- Hand-written `bv_decide` calls have an explicit 120 s SAT timeout.
