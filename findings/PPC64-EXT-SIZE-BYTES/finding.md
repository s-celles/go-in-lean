# PPC64-EXT-SIZE-BYTES: `int32(int16(x >> 1))` keeps 32 bits on ppc64/ppc64le (byte vs bit units)

**Classification:** `go_discrepancy_reproduced`. **Potentially novel compiler miscompilation.**
**Severity:** medium for ppc64/ppc64le: a narrowing conversion after a right shift is dropped
in ordinary code (power8 and power9 targets, both endiannesses).
**Security:** a dropped truncation can turn an in-range index into an out-of-range one (the fuzz
case panicked on a table lookup); no evident exploitable path. Private until reviewed.
**Human review status:** pending. Not reported upstream.

## Summary

`PPC64.rules` ("Eliminate unnecessary sign/zero extend following right shift", go1.21.13 ..
master `babb75be`; go1.19 had `sizeof(x.Type) <= 16`):

```
(MOV(WZ|W)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() <= 32 => (S(R|RA)Wconst [c] x)
(MOV(HZ|H)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() <= 16 => (S(R|RA)Wconst [c] x)
(MOV(BZ|B)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() == 8 => (S(R|RA)Wconst [c] x)
```

`Type.Size()` counts bytes; the conditions compare it with bit widths. The H rule therefore
always fires and drops the 16-bit extension of any 32-bit right shift; the B rule fires exactly
for 64-bit operands. The W rule always fires too but is harmless (`SRW`/`SRAW` already produce
an extended 32-bit result). Trace (go1.27.3): `MOVHreg <int16> (SRAWconst [1] x)` ->
`SRAWconst [1] x`; `int32(int16(x >> 1))` compiles to a single `SRAW $1, R3, R3`.

Even `Size() <= 2` would not be sound (a 16-bit value's register is not guaranteed extended),
so `fix.patch` (against master `babb75be`) deletes the H and B rules; the pattern-based rules
just above them (`(MOV(H|W)reg (SRAWconst [c] (MOVHreg x)))`, …) still cover extended operands.
With the fix, `go test -count=1 cmd/internal/testdir -run Test/codegen` passes, so no codegen
expectation depends on the deleted rules.

## Reproducer

```go
//go:noinline
func f(x int32) int32 { return int32(int16(x >> 1)) }
// GOARCH=ppc64le: f(-1 << 31) == -1073741824. Spec: int16(-2^30) == 0.
// Also uint32(uint16(x >> 1)) and int16(int32(x)>>8) < -513 (true for x = 0x80000000; spec false).
```

## Versions tested (2026-11-02, qemu-ppc64le/qemu-ppc64 11.1.2, -cpu power9)

| Toolchain | ppc64le | ppc64 |
|---|---|---|
| go1.21.13 | wrong | n/a |
| go1.25.5, go1.26.10, go1.27.3 (GOPPC64=power8 and power9) | wrong | wrong |
| master `babb75be` | wrong | wrong |
| master `babb75be` + `fix.patch` | correct | correct |

Controls: 386, arm, mipsle, amd64, arm64 correct. With the fix (together with the other fixes
of this repository) on master: `go test -short cmd/compile/internal/ssa cmd/compile/internal/test`,
`go test -count=1 cmd/internal/testdir -run Test/codegen` and `-run Test/fixedbugs` pass.

## Lean model (`property.lean` = `GoInLean/Compiler/PPC64ExtShift.lean`)

* `movhreg_sraw_refuted`, `movhzreg_srw_refuted`, `movbreg_sraw_refuted`, `movbzreg_srw_refuted`:
  kernel-checked counterexamples (`x = 0x80000000`, `c = 1`).
* `movwreg_sraw_sound`, `movwzreg_srw_sound`: the W rule is sound.
* `movhreg_sraw_movhreg_sound`, `movhzreg_srw_movhzreg_sound`, `movhreg_sraw_c16_sound`: the
  remaining rules are sound.

## How it was found

`scripts/cross_campaigns.sh` with `GOPPC64=power9`: seeds 50589 (go1.27.3, branch condition
`int16((int32(x) >> 8)) < -513` taken) and 50694 (master, index mode: a table index that should
be 0 became negative and panicked).

## Known-issue search (2026-11-02)

GitHub search on golang/go ("ppc64 sign extension shift int16 wrong", "ppc64 Type.Size bytes
bits rules", "ppc64le miscompile int16 conversion"): no match.
