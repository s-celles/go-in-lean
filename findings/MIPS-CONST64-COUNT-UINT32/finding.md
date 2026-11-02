# MIPS-CONST64-COUNT-UINT32: constant 64-bit shift counts ≥ 2^32 truncated on mips/mipsle

**Classification:** `go_discrepancy_reproduced`. **Potentially novel compiler miscompilation.**
**Severity:** low-medium: needs a constant count ≥ 2^32 created by merging two shifts after
decomposition (e.g. `(x >> 7) >> (uint64(y) | 0xFFFFFFFF)`); silent wrong value.
**Security:** no evident security impact. Private until reviewed.
**Human review status:** reviewed and approved by the maintainer of this repository on 2026-11-02; reported upstream as [golang/go#82776](https://github.com/golang/go/issues/82776). Distinct from golang/go#82772 (same port).

## Summary

`MIPS.rules:58-79` lower shifts by a constant 64-bit count with conditions on `uint32(c)`:

```
(Rsh8x64 x (Const64 [c])) && uint32(c) < 8  => (SRAconst (SLLconst <typ.UInt32> x [24]) [int32(c+24)])
(Rsh8x64 x (Const64 [c])) && uint32(c) >= 8 => (SRAconst (SLLconst <typ.UInt32> x [24]) [31])
... (18 rules, all widths, Lsh/Rsh/RshU)
```

`ARM.rules` and `386.rules` use `uint64(c)`. The lowering assumes `dec64` split every 64-bit
count, but the generic merging rule `(Rsh8x64 (Rsh8x64 x (Const64 [c])) (Const64 [d])) &&
!uaddOvf(c,d) => (Rsh8x64 x (Const64 <t> [c+d]))` fires again in `late_opt`, after
decomposition. In `(x >> 7) >> (uint64(y) | 0xFFFFFFFF)` the low word of the count folds to
0xFFFFFFFF, the high word is OR-ed away, and the two shifts merge into `x >> 4294967302`, which
the MIPS rules lower as `x >> 6` (`SLL $24; SRA $30`).

Fix (`fix.patch`, against master `babb75be`): `uint32(c)` -> `uint64(c)` in the 18 rules.

## Reproducer

```go
//go:noinline
func f(x, y int8) int8 { return (x >> 7) >> (uint64(y) | 0xFFFFFFFF) }
// GOARCH=mipsle or mips: f(127, -128) == 1. Spec: 127 >> 7 == 0, and 0 >> anything == 0.
```

## Versions tested (2026-11-02, qemu-mipsel/qemu-mips 11.1.2)

| Toolchain | mipsle | mips |
|---|---|---|
| go1.21.13, go1.25.5, go1.26.10, go1.27.3 | wrong | wrong (go1.27.3) |
| master `babb75be` | wrong | wrong |
| master `babb75be` + `fix.patch` | correct | correct |

Controls: 386 and arm correct (`uint64(c)` in their rules). With the fix on master,
`go test -short cmd/compile/internal/ssa cmd/compile/internal/test` and the codegen and
fixedbugs tests pass.

## Lean model (`property.lean` = `GoInLean/Compiler/MIPSConstCount.lean`)

* `merged_count`: `7 + 0xFFFFFFFF = 4294967302` (no unsigned overflow).
* `rsh8x64_refuted`: the rule pair yields 1 for `127 >> 4294967302`, Go 0 (kernel-checked).
* `rsh8x64_fixed`: with `uint64(c)` the lowering matches Go for every 64-bit count.
* `rsh8x64_ok_below_2_32`: the current rules are sound for counts below 2^32.

## How it was found

`scripts/cross_campaigns.sh` with `GOMIPS=softfloat`, seed 52073 on master (which already carries
the golang/go#82772 fix): `((-(-(int8(x) >> 7))) >> (uint64(y) | 4294967295))`.

## Known-issue search (2026-11-02)

GitHub search on golang/go ("mips shift count 32 bits uint32 Const64", "mipsle shift wrong
result large count"): no match.
