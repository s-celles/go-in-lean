# ARM64-CSINV-NOT: constant-flag `CSINV` folds to a boolean `Not` on arm64 (`^y` becomes `y ^ 1`)

**Classification:** `go_discrepancy_reproduced`. **Potentially novel compiler miscompilation.**
**Severity:** medium: arm64 is a first-class port (Apple Silicon, Graviton). The trigger needs a
conditional select whose condition becomes constant only after lowering, which is uncommon.
**Security:** no evident security impact. Private until reviewed.
**Human review status:** pending. Not reported upstream.

## Summary

`ARM64.rules` (go1.21.13 .. master `babb75be`):

```
(CSNEG [cc] _ y flag) && ccARM64Eval(cc, flag) < 0 => (NEG y)
(CSINV [cc] _ y flag) && ccARM64Eval(cc, flag) < 0 => (Not y)
(CSINC [cc] _ y flag) && ccARM64Eval(cc, flag) < 0 => (ADDconst [1] y)
```

`CSINV` selects the bitwise complement of `y` when the condition is false. The middle rule
emits `Not`, the generic *boolean* negation, which arm64 lowers as `(XOR (MOVDconst [1]) x)`:
the result is `y ^ 1`. Fix (`fix.patch`, against master `babb75be`): `(MVN y)`.

Trace (go1.27.3): `CondSelect (Com64 y) (Rsh64x64 x 33) (Less8 -17 (OnesCount8 128))` becomes
`CSINV [GreaterEqual] (SRAconst [33] x) y flags`; the `OnesCount8` table load from a constant
string folds to 1 inside `lower`, the flags become `FlagConstant`, and
`CSINV -> Not y -> XOR y 1 -> XORconst [1] y`. Assembly: `EOR $1, R1, R0; RET`.

## Reproducer

```go
//go:noinline
func f(x, y int64) int64 {
	r := x >> 33
	if bits.OnesCount8(128) > 0 { // always true
		r = ^y
	}
	return r
}
// GOARCH=arm64: f(0, 2) == 3. Spec: ^2 == -3. amd64 prints -3.
```

## Versions tested (2026-11-02, darwin/arm64 natively; linux/arm64 under qemu for the fix)

| Toolchain | arm64 |
|---|---|
| go1.21.13, go1.22.12, go1.23.12, go1.24.0, go1.25.5, go1.26.10, go1.27.3 | wrong (3, 1) |
| master `babb75be` | wrong |
| master `babb75be` + `fix.patch` | correct (-3, -1) |

Control: amd64 (Rosetta) correct.

## Lean model (`property.lean` = `GoInLean/Compiler/ARM64CondSelect.lean`)

`csinv_not_refuted`, `csinv_not_unsound` (kernel-checked: `^2 = -3`, lowered `Not 2 = 3`),
`csinv_mvn_fixed`, the CSNEG/CSINC siblings, and `not_ne_mvn` (the two never agree).

## How it was found

`scripts/cross_campaigns.sh` with `--bits` (math/bits intrinsics), seed 62089 (go1.27.3,
arm64 under qemu, `--branchy`); reproduced natively on darwin/arm64.

## Known-issue search (2026-11-02)

GitHub search on golang/go ("arm64 CSINV", "arm64 conditional select complement wrong",
"ccARM64Eval"): no match (golang/go#30679 is an unrelated internal compiler error).

With the fix on master: `go test -short cmd/compile/internal/ssa cmd/compile/internal/test`,
`go test -count=1 cmd/internal/testdir -run Test/codegen` and `-run Test/fixedbugs` pass.
