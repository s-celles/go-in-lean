<h1>
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/brand/lockup-dark.svg">
    <img alt="go-in-lean" src="assets/brand/lockup.svg" height="56">
  </picture>
</h1>

**Finding correctness bugs in Go's standard library with Lean 4: a proof-of-concept.**

go-in-lean models a bounded subset of Go (fixed-width integers and, so far,
the whole of `math/bits`) in Lean 4, states the documented behaviour of each
function as a theorem, proves it with Lean's kernel and `bv_decide`, and
turns every failed proof into a concrete Go test that is run against the
pinned Go toolchain. A failed proof is never reported as a Go bug: every
model counterexample must reproduce in Go, and every reproduced discrepancy
is checked against known issues and left for human review.

It is inspired by [julia-in-lean](https://github.com/MilesCranmer/julia-in-lean)
and differs from Gobra/Viper and Goose/Perennial in targeting bit-precise,
executable, kernel-checked models of *existing* library code rather than
annotated verification of new code (see `docs/prior-art.md`).

## Status (2026-11-01)

| | |
|---|---|
| Go version modelled | go1.25.5: all of `math/bits`; `slices.Compact/Index/Contains/Insert/Delete/Replace/Concat/Repeat`, `sort.Search`, `strings`/`bytes` `Repeat`/`Join` guards; 12 families of `generic.rules` + 74 generated constant folds; all 96 instances of the ARM64 and of the AMD64 shift-lowering rules, the rotate lowering rules of both; 64-bit targets |
| Lean | 4.35.0, no Mathlib, zero Lake dependencies |
| Properties registered | 68 (`targets/properties.yaml`) |
| Proved in model | 2,209 audited theorems (600 kernel-only, 1,609 `bv_decide`): `math/bits` in full, slices/sort/strings guards, 896 generated `generic.rules` instances (incl. bounds-check and rotate rules), 644 magic-division instances, ARM64/AMD64 shift and rotate lowering, the new `knownbits` pass and the interval arithmetic of `prove` on Go master, and the MIPS, riscv64 and s390x rules behind three findings |
| Checked exhaustively, not proved | `slices.Insert/Delete/Replace` with aliasing: 531,531 configurations vs spec, 16,128 replayed through real Go |
| Metamorphic fuzzing | `scripts/metamorphic_fuzz.py`: constant vs run-time vs inlined versions of random integer expressions; 400 seeds (go1.27.3, master, amd64) and 2,160 seeds on nine other architectures under qemu (`scripts/cross_campaigns.sh`) |
| **Compiler bugs found** | (1) `((x >> c) & d) << e` rules compare constant counts as signed: wrong code in go1.25–1.27 and master; reported as [golang/go#82763](https://github.com/golang/go/issues/82763). (2) Master-only regression: shift-composition rules type the combined count with the shifted value's type and master's `prove` now trusts it: `(int32(2) >> 1) >> (1<<62)` is 1 (spec 0); fix validated; reported as [golang/go#82767](https://github.com/golang/go/issues/82767), `findings/SSA-COMPOSE-CONST64-TYPE` |
| **Architecture-specific miscompilations** | (3) mips/mipsle: `Rsh8x*` sign-extends from bit 15 (since go1.8; [golang/go#82772](https://github.com/golang/go/issues/82772)). (4) riscv64, go1.26 regression: `int8(x - (-x)) >> 8` compiles to 0 ([golang/go#82773](https://github.com/golang/go/issues/82773)). (5) s390x, since go1.26: `uint64(int8(-128)) < 0xFFFFFFFF` is true ([golang/go#82774](https://github.com/golang/go/issues/82774)). Fixes validated on master; reported after human review |
| Other discrepancies | `strings`/`bytes` `Join` conservative overflow guard (`unsafe` only, negligible); two latent rules wrong for unreachable counts (AMD64 `CMPLconst (SHRLconst _ [32])`, generic rotate recognition with a count ≥ 2^63) |
| Known issues reproduced | golang/go#54255, golang/go#15175 |
| Mutation test | 8 mutants refuted in Lean and reproduced in Go |

## Quick start

Prerequisites: [elan](https://github.com/leanprover/elan) (installs Lean
4.35.0 from `lean-toolchain`), Go 1.25.x, Python 3 (standard library only).
With Nix: `nix develop` provides elan, Go and Python.

```sh
lake build                 # models, specifications, proofs (≈1 min)
lake exe audit             # axioms used by every theorem (kernel / bv_decide tiers)
scripts/check.sh           # everything CI runs, see below
```

`scripts/check.sh` runs, in order: banned-tactic source scan; regeneration
check of the generated files (Go lookup tables, constant-folding theorems);
`lake build`; axiom audit; `go vet` and the Go property tests (math/big
oracle, exhaustive 8/16-bit checks, boundary values); differential vectors
(47k inputs computed by Go, re-evaluated by the Lean models); bounded
exhaustive slice search and Go replay of 16k aliasing configurations;
manifest validation; mutation test (5 mutants → `bv_decide` counterexamples
→ generated Go reproducers → `go test`).

## Layout

```
GoInLean/Semantics/     Go integer semantics (BitVec + panics), validation, oracle specs
GoInLean/Stdlib/        transliterated Go code (+ generated tables)
GoInLean/Properties/    theorems, one per manifest entry
GoInLean/Audit.lean     axiom audit executable
GoInLean/CheckVectors.lean  differential checker executable
mutants/                deliberately wrong models (success criterion 6)
go/tests/               Go property tests and vector generator
go/reference/           Go twins of the mutants
go/reproducers/         generated reproducers (one per Lean counterexample)
targets/properties.yaml property manifest with status history
findings/               reproduced findings awaiting human review (none yet)
scripts/                check.sh, gen_bits_tables.py, validate_manifest.py, mutation_test.py,
                        gen_brand.py (visual identity)
docs/                   prior-art, semantic-boundary, architecture, compiler feasibility, report, brand
assets/brand/           logo, lockups, favicon, social preview (generated, see docs/brand.md)
```

## Reading the results

* `proved_in_model` means the *transliterated algorithm* satisfies the
  specification; the model is tied to Go by differential testing and
  reviewable line-by-line transliteration, not by proof
  (`docs/semantic-boundary.md`, assumption A4 on compiler intrinsics).
* Theorems proved with `bv_decide` rely on a per-theorem native-evaluation
  axiom (`…._native.bv_decide.ax_…`, the verified LRAT checker run through
  the compiler); `lake exe audit` reports the tier of every theorem.
  `native_decide` and `sorry` are banned.
* `docs/research-report.md` lists every property investigated with its
  classification, the limitations, and the prioritised next steps.

## Contributing

See `AGENTS.md` for commit conventions. Do not file upstream Go issues from
pipeline output without human review of the finding directory.

## Licence

MIT (see `LICENSE`). Transliterated Go code and generated tables are
derived from Go sources under the BSD 3-Clause licence (see `NOTICE`).
