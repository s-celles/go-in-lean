# go-in-lean

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
| Go version modelled | go1.25.5: all of `src/math/bits/bits.go`; `slices.Compact/Index/Contains`, `sort.Search` (list model); 12 families of `generic.rules`; 64-bit targets |
| Lean | 4.35.0, no Mathlib, zero Lake dependencies |
| Properties registered | 46 (`targets/properties.yaml`) |
| Proved in model | 38 entries, 187 audited theorems (67 `bv_decide`, 120 kernel-only): every `math/bits` function at every width (incl. de Bruijn `TrailingZeros64`, SWAR `OnesCount64`, carry/borrow formulas, the Knuth `Div64` algorithm at width 8), `sort.Search`, `slices.Compact/Index/Contains`, strength-reduction / shift / bounds-check compiler rules, 74 generated constant-folding rules |
| Checked exhaustively, not proved | `slices.Insert/Delete/Replace` with aliasing on the backing-array model: 531,531 configurations vs spec, 16,128 replayed through real Go, 0 mismatches |
| Inconclusive | `Mul64` and `Div64` at 64 bits (SAT budget; proof automation, not counterexamples) |
| Known issues reproduced | Add64 with carry = 2 (golang/go#54255, documented precondition); the Go 1.6 `Rsh8Ux64` constant-folding rule (golang/go#15175) refuted in the model |
| New Go bugs | none found; `math/bits` behaved as documented on everything proved and tested |
| Model/spec errors caught by proofs | 4 model mismatches (Go vs Lean operator precedence) and 2 specification errors (power-of-two side condition), all before any claim about Go |
| Mutation test | 5 deliberately faulty models refuted in Lean and reproduced against Go mutants |

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
scripts/                check.sh, gen_bits_tables.py, validate_manifest.py, mutation_test.py
docs/                   prior-art, semantic-boundary, architecture, compiler feasibility, report
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
