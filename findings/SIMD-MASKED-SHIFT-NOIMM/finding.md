# SIMD-MASKED-SHIFT-NOIMM — IfElse(shift) on amd64/AVX-512 fails to build (missing immediate)

**Status: to report** (repro fails on master 740d909bb5; the fix (fix.patch) builds the full 11-case matrix, 25/25 fuzzer seeds agree across GODEBUG=auto/0/128/256, and the directed IfElse semantics test passes: masked-off lanes keep the false operand)

## Summary
With GOEXPERIMENT=simd on amd64, `x.ShiftAllLeft(c).IfElse(mask, y)` (any constant
shift count, any 16/32/64-bit integer vector type, both shift directions) fails to
compile when the 512-bit variant is generated:

```
main.f@simd512: invalid instruction: 00007 (...)\tVPSLLQ\tZ0, K1, Z1
```

The IfElse lowering fuses the shift into a merge-masked EVEX instruction
(`VPSLLQMasked512constMerging`, reg `w2kw`, aux `UInt8`), but the code-generation
helper `simdV2kvResultInArg0` (cmd/compile/internal/amd64/ssa.go) never emits
`v.AuxInt` as an immediate. The assembler receives a 3-operand `VPSLLQ Z0, K1, Z1`
and no entry in its ytab matches (the masked immediate-shift EVEX form requires
the `Yu8` immediate as the first operand), so obj rejects the instruction the
compiler itself emitted. The sibling helper `simdVfpkv` documents the expected
operand layout (`VPSLLQ Z1, X1, K1, Z2`).

Same family as golang/go#82745 (assembler rejects a compiler-emitted EVEX
instruction) but a distinct root cause: a missing immediate operand, not a merged
memory operand.

## Reproducer (3 lines, valid Go)
```go
//go:build goexperiment.simd
package main

import "simd"

func f(x, y simd.Uint64s, m simd.Mask64s) simd.Uint64s {
	return x.ShiftAllLeft(2).IfElse(m, y)
}
```
`GOEXPERIMENT=simd go build` → `main.f@simd512: invalid instruction: VPSLLQ Z0, K1, Z1`.
Compile-time failure only (no wrong code emitted); 128/256-bit variants are fine.

## Scope (validated empirically, matrix of 11 type x op cases)
- All of Int16s/Uint16s/Int32s/Uint32s/Int64s/Uint64s (shifts), ShiftAllLeft and
  ShiftAllRight (Int64s has no ShiftAllRight), @simd512 variant only.
- Affected instructions seen: VPSLLW/VPSLLD/VPSLLQ/VPSRAW/VPSRAD/VPSRAQ/VPSRLW/
  VPSRLD/VPSRLQ (the `...MaskedNNNconstMerging` ops).
- Found by scripts/simd_fuzz.py seed 2 expr 21 and seed 24 expr 16 (cross-config
  differential fuzzer for the goexperiment.simd package; the compile failure
  surfaced during the generator's build-validation loop).

## Root cause
cmd/compile/internal/amd64/ssa.go, `simdV2kvResultInArg0`:

```go
p.From.Type = obj.TYPE_REG
p.From.Reg = simdReg(v.Args[1])     // source only
p.AddRestSourceReg(maskReg(v.Args[2]))
p.To.Type = obj.TYPE_REG
p.To.Reg = simdReg(v)
// v.AuxInt (the shift count) is never emitted
```

Fix: when the op carries an aux (`ssaop.OpcodeTable[v.Op].AuxType != AuxTypeNone`),
emit `p.From` as TYPE_CONST with `v.AuxInt` and the source as a rest source, so the
prog matches the assembler's `{Yu8, Yzm, Yknot0, Yzr}` operand order.

## Classification
Not a security issue: compile-time failure, no incorrect code is produced.
No duplicate found upstream (searched "VPSLLQ", "invalid instruction" + simd; the
closest is #82745, different cause).
