# MIPS-RSH8-SIGNEXT16: signed 8-bit variable right shifts sign-extend from bit 15 on 32-bit MIPS

**Classification:** `go_discrepancy_reproduced`. **Potentially novel compiler miscompilation.**
**Severity:** medium for the affected ports: silent wrong code for ordinary source (`int8`
arithmetic followed by `>>` with a non-constant count), no unusual constants needed.
Only `GOARCH=mips` and `GOARCH=mipsle` are affected (both endiannesses).
**Security:** no evident security impact; handled as a private report until reviewed.
**Human review status:** reviewed and approved by the maintainer of this repository on 2026-11-02; reported upstream as [golang/go#82772](https://github.com/golang/go/issues/82772).

## Summary

`src/cmd/compile/internal/ssa/_gen/MIPS.rules:116-118` (go1.27.3, unchanged on master
`babb75be`; the same text exists since go1.8, when the 32-bit MIPS port was added):

```
(Rsh8x32 x y) => (SRA (SignExt16to32 x) ( CMOVZ <typ.UInt32> y (MOVWconst [31]) (SGTUconst [32] y)))
(Rsh8x16 x y) => (SRA (SignExt16to32 x) ( CMOVZ <typ.UInt32> (ZeroExt16to32 y) (MOVWconst [31]) (SGTUconst [32] (ZeroExt16to32 y))))
(Rsh8x8 x y)  => (SRA (SignExt16to32 x) ( CMOVZ <typ.UInt32> (ZeroExt8to32 y) (MOVWconst [31]) (SGTUconst [32] (ZeroExt8to32 y))))
```

`x` is an 8-bit value; the bits of its 32-bit register above bit 7 are unspecified (for example
the raw result of `MUL` or `ADDU`). The rules sign-extend from bit 15 (`SignExt16to32`, i.e.
`MOVHreg`) instead of bit 7, so bits 8-15 of the register take part in the arithmetic shift.
Every other signed 8-bit rule in `MIPS.rules` uses `SignExt8to32` (`Div8`, `Mod8`, `Less8`, the
constant-count `Rsh8x64`), and `MIPS64.rules` uses `SignExt8to64`. The fix replaces
`SignExt16to32` by `SignExt8to32` in the three rules (`fix.patch`, against master `babb75be`).

When `x` was loaded from memory with `MOVB` the register is already sign-extended from bit 7
and `MOVHreg` is harmless (Lean: `rsh8x32_ok_if_extended`), which explains why the defect
went unnoticed.

## Minimal reproducer

```go
//go:noinline
func mulShr8(x, k int8, s uint64) int8 { return (x * k) >> s }
// GOARCH=mipsle or mips: mulShr8(127, -15, 8) == -8. Spec: int8(127*-15) == -113; -113 >> 8 == -1.
// Also (x+k)>>s with 127, 1, 8 gives 0 (spec -1), and (x*k)>>3 gives 17 (spec -15).
```

Assembly (go1.27.3, `GOARCH=mipsle`, `-gcflags=-S`): `MUL R2, R1, R1; MOVH R1, R1; … ; SRA R2, R1, R1`.
The defect is visible in the generated code; qemu only confirms the consequence.

`reproducer_test.go` (also `go/reproducers/finding_mips_rsh8_test.go`, build tag
`reproduce_findings`) asserts the specification:

```
GOOS=linux GOARCH=mipsle go test -c -tags reproduce_findings -o r.test ./reproducers
qemu-mipsel ./r.test -test.run MIPSRsh8 -test.v
```

## Versions tested (2026-11-02)

| Toolchain | mipsle | mips | controls (386, arm, mips64le) |
|---|---|---|---|
| go1.25.5 | wrong (-8, 0, 17) | n/a | n/a |
| go1.27.3 | wrong (-8, 0, 17) | wrong | correct |
| master `babb75be` | wrong (-8, 0, 17) | wrong | n/a |
| master `babb75be` + `fix.patch` | **correct** | **correct** | n/a |

With `fix.patch` on master, `go test -short cmd/compile/internal/ssa cmd/compile/internal/test` passes.

## Lean model

`property.lean` (= `GoInLean/Compiler/MIPSShift8.lean`) models 32-bit registers with arbitrary
upper bits, `CMOVZ`/`SGTUconst` clamping, and `SRA` (count masked to 5 bits):

* `rsh8x32_refuted`, `rsh8x32_unsound`: kernel-checked counterexample (register `0xF88F`, count 8).
* `rsh8x32_fixed`, `rsh8x16_fixed`, `rsh8x8_fixed`: the rules with `SignExt8to32` are sound for
  every register value and count (bv_decide).
* `rsh8x32_ok_if_extended`: the current rule is sound on already-extended registers.
* `rsh16x32_sound`: the 16-bit rules are correct; the defect is specific to 8 bits.
* `spec_eq`: the case-split specification equals `BitVec.sshiftRight'`.

## How it was found

`scripts/cross_campaigns.sh` (new) runs `scripts/metamorphic_fuzz.py` for nine `GOARCH`
values under qemu user-mode emulation on an amd64 host. The first run found 12 of 60 mipsle
seeds failing on go1.27.3 and 12 of 60 on master, with every other 32-bit port clean. All
mismatches were `int8` expressions shifted right by a constant ≥ 8 where only the run-time
count version disagreed; the minimal program and the assembly followed.

## Known-issue search (2026-11-02)

GitHub search on golang/go for "mips shift int8 sign", "SignExt16to32 mips", "Rsh8x32 MIPS":
no match.
