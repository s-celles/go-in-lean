# Changelog

All notable changes to this project are documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.1.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).
No version has been released yet; everything below is unreleased work since the
first commit (2026-11-01). Upstream issue and CL states are tracked in
`docs/upstream-status.md`.

## [Unreleased]

### Added

- Campaign 6 of `ssa_tv.py` on OPTIPLEX7010 (seed 20261127): arm lowered (go1.27.3 and
  tip), 386 and mipsle generic, `core`/`bits`/`ext`, optimized and `-N -l`; 14,400
  function checks, 82,319 pass pairs, no report (`docs/research-report.md` 3.23).
- `ssa_tv.py` on the 32-bit targets (386, arm, mipsle): the dec64 operations that split
  64-bit values, parameter halves, the ABI0 result and parameter slots, and ABI0 calls to
  `b2i`. `--lowered` now covers 32-bit arm (about 150 operations) and finds
  golang/go#82786 at `lower`. Read-only string tables such as `math/bits`' `len8tab` are
  modelled. Big-endian mips is reported as unsupported (`docs/research-report.md` 3.23).
- Local verification of CL 862781 (golang/go#36897): the reproducer is fixed, and an
  `ext` sweep (3,000 functions, amd64 `-N -l`) gives 8 reports on go1.27.4 and none with
  the CL; posted on the CL as a top-level comment on 2026-11-16
  (`findings/AMD64-ANDL-MINUS1-ZEXT-NOOPT/cl/comment-cl862781.md`).
- A patchset 2 for CL 858581 (golang/go#82839), prepared after review: the check moves
  from the extension case of `prove` into the `x+delta` constant case, where the constant is
  truncated; validated locally and uploaded on 2026-11-16 with the review replies
  (`docs/cl-verification.md`).
- A generated Hugo/Hextra documentation and findings website, with strict Go
  YAML validation, per-property and per-finding evidence pages, computed status
  and trust counts, local search, filterable/sortable registries inspired by
  julia-findings, and GitHub Pages deployment. Finding metadata
  now has one YAML manifest per existing research record. Hugo Extended 0.152.2
  and Hextra v0.13.0 are pinned; Nix and CI use the same Hugo release.
  Published at [s-celles.github.io/go-in-lean](https://s-celles.github.io/go-in-lean/).
- Generator checks for registry coverage, deterministic output, invalid YAML,
  status histories, upstream table parsing, and safe content replacement.
- A direct exhaustive `bits.ReverseBytes16` check in the CL 857542 regression
  test, covering all 65,536 inputs alongside the original Power10 miscompilation
  reproducer, in response to review feedback; an incremental patch against
  PS2, a review reply, and before/after validation on both PPC64 byte orders.
  Published as patchset 3 on 2026-11-14; review request resolved.
- Campaign 5 of `ssa_tv.py --lowered` on OPTIPLEX7010 (seed 20261126): `core`/`bits` under
  `-N -l` on amd64, ppc64le, loong64 and riscv64, `bits` on arm64 and s390x, arm64 with tip;
  about 13,200 function checks, no report (`docs/research-report.md` 3.19).
- ARM64 stack accesses in `scripts/ssa_tv.py --lowered`, including signed/unsigned
  loads, partial stores and `MOVDaddr`, so `--gcflags "-N -l"` can validate debug
  builds. A go1.27.4 search on VASSIVIERE checked 1,800 generated functions across
  `core`, `ext` and `bits`, optimized and debug builds, with no new compiler report
  (`docs/research-report.md` 3.22).
- `scripts/ssa_tv.py --lowered` support for ARM64 integer ops, NZCV conditions and conditional selects. Directed tests reproduce golang/go#82777; after correcting two validator-model errors, the `core`/`ext` sweep reported no new defect (`docs/research-report.md` 3.21).
- `scripts/ssa_tv.py --lowered` support for s390x compare, condition-code, conditional-select
  and integer register operations. Directed tests detect the known #82774 mismatch on
  go1.27.3 and agree with native evaluation on clean functions; an optimized `core`/`ext`
  search of 2,400 function checks on OPTIPLEX7010 produced no new report
  (`docs/research-report.md` 3.20).
- Follow-up `ext` symbolic sweep on OPTIPLEX7010 (seed 20261123): 60 programs across
  amd64, ppc64le power8/power10, loong64 and riscv64, with go1.27.3 and tip, under
  `-N -l` (6,000 function checks, 34,120 pass pairs). It reproduced only tracked issues
  #36897, #82775 and #82782; exact-function checks and native amd64 runs confirmed the
  counterexamples (`docs/research-report.md` 3.19).
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

- Expanded `AGENTS.md` with finding deduplication, reproducible evidence,
  human-controlled classifications, upstream publication scope, privacy and
  private handling of potentially memory-unsafe findings. Aligned the Gerrit
  instructions with explicitly authorized publication after human review.
- Moved the full README content into `docs/project.md`, published as the site's
  project guide and linked from the dashboard and documentation navigation.
  The README is now a short introduction linking to the site. Site generation
  reads the guide independently of the README and preserves links to former
  README sections.
- Refreshed the upstream status snapshot on 2026-11-14, including the merged
  Loong64 fix and the published Power10 direct-test follow-up.
- All written artifacts are in English (2026-11-04).
- The README states the scope of upstream contributions: reports with a reproducer and
  an analysis, no pull request offered by default, and a courteous request to flag any
  mistaken or debatable report.

### Fixed

- `ssa_tv.py`: the arm model read a flags argument for every register-shift operation
  (`ORshiftLLreg`, `CMPshiftLLreg`, ...), which crashed it; only `ADC`/`SBC`/`RSC` read
  flags. An unexpected exception in the model is now reported as a `model_error` for that
  function instead of stopping the run.
- `ssa_tv.py` modelled the ARM/ARM64 `Noov` conditions as `lt ∧ ¬V` and `ge ∧ ¬V`; gc
  emits `MI`/`PL` for them, which test N alone.
- Reworded a documentation comment in the float-rounding proof to avoid a
  false positive in the existing banned-token scan; no proof is changed.
- ARM64 SSA validation now materializes comparison results as integer 0/1 when
  consumed by register operations or merged with integer values in a phi. This
  includes the pending bool-`NEG` correction and clears seven encoding failures
  found by the new campaign; regression tests cover arithmetic, comparisons,
  mixed phis and native evaluation.
- The metamorphic fuzzer silently skipped programs that did not compile.
- The `--carry` mode now masks the borrow input to 0 or 1.
- Hand-written `bv_decide` calls have an explicit 120 s SAT timeout.
