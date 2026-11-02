# RISCV64-SLLI-NARROW-TYPE: `int8(x - (-x)) >> 8` compiles to 0 on riscv64 (Go 1.26 regression)

**Classification:** `go_discrepancy_reproduced`. **Potentially novel compiler miscompilation.**
**Severity:** medium for riscv64: silent wrong constant for ordinary source, a regression in
go1.26. Only `GOARCH=riscv64` is affected.
**Security:** no evident security impact; handled as a private report until reviewed.
**Human review status:** reviewed and approved by the maintainer of this repository on 2026-11-02; reported upstream as [golang/go#82773](https://github.com/golang/go/issues/82773).

## Summary

Two `RISCV64.rules` rules interact:

```
(SRAI <t> [x] (MOVBreg y)) && x >=  8 => (SRAI  [63] (SLLI <t> [56] y))   // old
(SRAI <t> [x] (MOVHreg y)) && x >= 16 => (SRAI  [63] (SLLI <t> [48] y))   // old
(SLLI <t> [c] (ADD x x)) && c >= t.Size() * 8 - 1 => (MOVDconst [0])     // new in go1.26
```

The first rules move the byte (half-word) to the top of the 64-bit register and read bit 63,
but give the `SLLI` the narrow result type `t`. The go1.26 fold trusts `t`: modulo 2^8,
`(x+x) << c` is 0 once `c ≥ 7`, but the outer `SRAI [63]` reads the full register. The lowering
turns `x - (-x)` into `ADD x x` (`(SUB x (NEG y)) => (ADD x y)`), so the pattern arises from
plain source. Trace of the `lower` pass (go1.27.3):

```
v11 = Rsh8x64 v9 (63)        -> SRA (SignExt8to64 v9) ...  -> SRAI [63] (MOVBreg v9)
v9  = SUB v6 (NEG v6)        -> ADD v6 v6
SRAI [63] (MOVBreg v9)       -> SRAI [63] (SLLI <int8> [56] v9)
SLLI <int8> [56] (ADD v6 v6) -> MOVDconst [0]
```

Fix (`fix.patch`, against master `babb75be`): type the inner shift `<typ.Int64>` in the two
lowering rules. The sound rule `(SLLI [c] (ADD x x)) => (SLLI [c+1] x)` then applies.

## Reproducer

```go
//go:noinline
func f(x int8) int8 { return (x - (-x)) >> 8 }
// GOARCH=riscv64: f(-1) == 0. Spec: int8(-2) >> 8 == -1. Assembly: MOV $0, X10; RET.
// Same for int16 with >> 16, and for b := -a; (a - b) >> 9.
```

## Versions tested (2026-11-02, qemu-riscv64 11.1.2)

| Toolchain | Result |
|---|---|
| go1.22.12, go1.23.12, go1.24.0, go1.25.5 | correct |
| go1.26.10, go1.27.3 | **wrong** (0, 0, 0) |
| master `babb75be` | **wrong** |
| master `babb75be` + `fix.patch` | correct |

Controls: amd64, arm64, s390x correct on the same program. With the fix on master,
`go test -short cmd/compile/internal/ssa cmd/compile/internal/test` and
`go test -count=1 cmd/internal/testdir -run 'Test/codegen|Test/fixedbugs'` pass.

## Lean model (`property.lean` = `GoInLean/Compiler/RISCV64Narrow.lean`)

* `fold_low_byte`: the fold is true of the low byte; `fold_full_refuted`: not of the register.
* `srai_movbreg_sound`: the lowering rule is sound in 64 bits for all counts 8..63.
* `composite_refuted`: compiled 0 vs Go -1 for x = -1.
* `fixed_fold_sound`, `fixed_end_to_end`: with the fix, the lowering of `int8(x+x) >> k` matches Go.

## How it was found

`scripts/cross_campaigns.sh`, seed 40799 (go1.27.3, riscv64, `--branchy`):
`((int8(x) - (-int8(x))) >> uint64(63))`; only the constant-count versions disagreed.

## Known-issue search (2026-11-02)

GitHub search on golang/go ("riscv64 SLLI ADD", "riscv64 miscompile 1.26",
"riscv64 shift wrong result int8"): no match. Related class: golang/go#82767 (a node typed
narrower than the value it computes, trusted by a later transformation).
