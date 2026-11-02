# SSA-SHIFTMASK-SIGNED-COUNT: `((x >> c) & d) << e` rules miscompile constant shift counts ≥ 2^63

**Classification:** `go_discrepancy_reproduced`. **Potentially novel compiler miscompilation.**
**Severity:** low–medium: silent wrong code, but only for a *constant* shift count ≥ 2^63
applied to a *signed* value (reachable through inlining, see below).
**Security:** no evident security impact (pure arithmetic on a pathological count); still
handled as a private report.
**Human review status:** reviewed and approved by the maintainer of this repository on 2026-11-02; reported upstream as [golang/go#82763](https://github.com/golang/go/issues/82763).

## Summary

`src/cmd/compile/internal/ssa/_gen/generic.rules:522-530` (go1.25.5, unchanged on `master`
as of 2026-11-01; present in go1.26.10, go1.27.3 and master `babb75be`) rewrite `((x >> c) & d) << e` with constant `c`, `e` into a single shift
and a shifted mask. They choose the branch with the SIGNED comparisons `c >= e` / `c < e` on
the int64 AuxInts, and compute the new count as `e-c` or `c-e` in int64. Shift counts are
unsigned in Go: a constant count `c ≥ 2^63` is a negative AuxInt, so the `c < e` branch is
taken and `x << (e-c)` (a huge count) replaces a sign-filling right shift. For unsigned `x`
the inner shift is first folded to 0 by `generic.rules:446-449`; for signed `x` no such fold
exists, and the wrong rewrite fires.

## Minimal reproducer (go1.25.5, darwin/arm64 and amd64 via Rosetta)

```go
//go:noinline
func f(x int64) int64 { return ((x >> (1 << 63)) & 3) << 1 }
// f(-1) returns 0. Spec: -1 >> 2^63 == -1, & 3 == 3, << 1 == 6.
// The same expression with a variable count returns 6. Same result with -gcflags='-N -l'.
```

Reachable without a suspicious literal, through inlining:

```go
func field(x int64, shift uint64, mask int64) int64 { return (x >> shift) & mask }
const allBits = ^uint64(0)
//go:noinline
func g(x int64) int64 { return field(x, allBits, 3) << 1 }
// g(1) == 4 (spec: 0); g(-1) == 4 (spec: 6). With -gcflags=-l: 0 and 6. go vet is silent.
```

Extent (exhaustive small program, all signed/unsigned widths, counts {2^63, 2^63+5,
2^64-1, 2^64-2, 200}, d ∈ {1,3}, e ∈ {1,2,W-1}): 208 mismatches, all on signed types
int8/16/32/64 with c ≥ 2^63; none on unsigned types; none for c = 200.

## How it was found

`scripts/generic_rules_to_lean.py --triage` translated 830 rule instances of generic.rules to
Lean and bit-blasted each one (`targets/generic_rules_triage.json`). Nine instances
(`r527_0 … r530_1`) returned concrete counterexamples, all with a count ≥ 2^63 (e.g.
`c = 18446744073709551615`). The Go reproducer was then written from those values, and the
SSA dump (`GOSSAFUNC`) shows the input `Lsh64x64 (And64 (Rsh64x64 x (Const64 [-9223372036854775808]))
(Const64 [3])) (Const64 [1])` reduced to `Const64 [0]` by the `opt` pass.

## Versions tested (2026-11-02)

| Toolchain | arm64 | amd64 (Rosetta 2) |
|---|---|---|
| go1.25.5 | wrong (0, 4, 4) | wrong |
| go1.26.10 (latest 1.26) | wrong | wrong |
| go1.27.3 (latest release) | wrong | wrong |
| master `babb75be` (go1.28-devel, 2026-11-01) | wrong | wrong |
| master `babb75be` + `fix.patch` | **correct** (6, 0, 6) | n/a |

With `fix.patch` applied to master: the reproducer is correct, the exhaustive program goes from
208 mismatches to 0, and `go test cmd/compile/internal/ssa cmd/compile/internal/test` and
`go test cmd/internal/testdir -run 'Test/codegen/shift.go|Test/fixedbugs/issue1*'` pass (the
codegen test shows the optimisation still applies to ordinary counts).

## Proposed fix (proved in Lean, validated on master, not submitted)

`fix.patch` (8 lines of `_gen/generic.rules`; regenerate with `go run .` in `_gen`).

Add `c >= 0 && e >= 0` to the eight rules (equivalently compare as `uint64` and require both
counts < 2^63). `GoInLean/Compiler/ShiftMask.lean` proves all 16 fixed instances
(4 widths × signed/unsigned inner shift × 2 branches) for every x, d and every count pair
below 2^63, and refutes the current 64-bit signed `c < e` instance at the reproducer's inputs.

## Known-issue search (2026-11-01)

Web searches for the rule shape and symptoms found no matching report. Related but
different: golang/go#81869 / CL 795240 (shift canonicalisation typing), golang/go#64285
(riscv64 large shifts), golang/go#79886 (arm64 shift amount upper bits).

## Reproduction commands

```sh
lake build GoInLean.Compiler.ShiftMask
cd go && go test -tags reproduce_findings ./reproducers -run ShiftMask -v   # FAILS on go1.25.5
GOARCH=amd64 go test -tags reproduce_findings ./reproducers -run ShiftMask -v
```

## Limitations

* Executed on go1.25.5, go1.26.10, go1.27.3 and master `babb75be` (darwin/arm64, amd64 under Rosetta 2); not executed on other architectures (the bug is in architecture-independent rules).
* Reachability in real programs needs a constant shift count ≥ 2^63 after optimisation
  (literal, constant argument through inlining, or generic instantiation); such code is rare.

## Confidence

High: Lean counterexample, real-compiler reproduction on two architectures, variable-count
control, SSA dump identifying the rule, and a proved fix.
