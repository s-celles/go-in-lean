# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).
No version has been released yet; everything below is unreleased work since the
first commit (2026-11-01). Upstream issue and CL states are tracked in
`docs/upstream-status.md`.

## [Unreleased]

### Added

- `scripts/ssa_tv.py --lowered` on loong64 (about 80 ops; `DIVV`/`REMV` without a `-1` fix-up
  modelled with the Go result): it finds golang/go#82773, still open on loong64, at `lower`.
- `scripts/ssa_tv.py`: stack slots on ppc64/ppc64le, so `--lowered --gcflags "-N -l"` covers
  ppc64 debug builds too (232 of 240 generated functions supported, no report).
- Symbolic sweep with `ssa_tv.py --lowered` on OPTIPLEX7010 (21,600 function checks: `ext`,
  `core`, `bits`; amd64, riscv64, ppc64le; optimized and `-N -l`; go1.27.3 and tip): no false
  report; two more spellings of golang/go#82775 on ppc64le (`docs/research-report.md` 3.19).
- `scripts/ssa_tv.py --lowered` on riscv64 (about 75 ops: no flags, sign-extending `W`
  ops and loads, ISA-defined division): it finds golang/go#82773 at `lower` on go1.27.3
  (optimized and `-N -l`) and tip.
- `ext` suite in `scripts/alt_compiler_diff.py` (`ExtGen`): identity detours that only
  `-N` builds keep until the lowering (`e &^ (f ^ f)`, `e & ^(f - f)`, `e | (f - f)`, ...),
  nested conversions of mixed width and signedness, and `narrow(wide(e) >> c)`; the other
  suites' programs are unchanged. On 300 programs it found 5 instances of the golang/go#36897
  trigger (gc `-N` on amd64), all confirmed independently by `ssa_tv.py --lowered --gcflags
  "-N -l"` at `lower` (`docs/research-report.md` 3.19).
- `scripts/ssa_tv.py --lowered` on amd64 (about 150 ops with the x86-64 rules on upper
  bits, flags, masked shift counts and the division `-1` fix-up) and `--gcflags` for `-N -l`
  debug builds, with a byte-level model of stack slots and of the non-inlined `b2i`
  helper. It finds the golang/go#36897 trigger at `lower` under `-N`; 4,800 function
  checks of generated programs (go1.27.3 and tip, optimized and `-N -l`) gave no report.
- `scripts/ssa_tv.py --lowered`: the translation validation continues through the ppc64
  lowered passes (`lower` to `flagalloc`), with about 80 PPC64 ops modelled from
  `PPC64Ops.go` and the ISA (CR fields, `ISEL`, rotate-and-mask, `CC` tuples, divisions with
  the `-1` fix-up, ISA-undefined bits as free variables). It finds golang/go#82775 at `lower`;
  the counterexamples, run under qemu-ppc64le, give exactly the predicted values. Option
  `--timeout-ms`; solver timeouts are counted per pass pair instead of abandoning the function.
- **Long campaign, final totals** (2026-11-05 23:00 to 2026-11-06 16:21): 101,800 programs on
  amd64 and eleven qemu targets, no unexplained case (`docs/research-report.md` 3.17). The
  last step found a concrete trigger for golang/go#36897 (open since 2020): with `-N`, gc on
  amd64 drops the zero extension of `uint64(uint32(x) &^ (uint32(x) ^ uint32(x)))`
  (`findings/AMD64-ANDL-MINUS1-ZEXT-NOOPT/`).
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
