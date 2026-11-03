# AMD64-SBB-CARRYMASK-FLAGS: SBB carry masks are not marked clobberFlags, so a flag value survives a flag clobber

**Classification:** `go_discrepancy_reproduced`. **Compiler miscompilation (wrong code),
amd64 and 386.** Plain safe Go code computes a wrong boolean.
**Affected:** go1.24.13 .. go1.27.3 and master `2b74366d` on amd64 (all GOAMD64 v1-v3);
the 386-only variant below affects go1.24.13 .. go1.27.3 (master's shift-lowering rework
removes that shape, not the defect).
**Human review status:** reviewed 2026-11-03 — classified as an ordinary miscompilation
(no memory-safety impact; bounds checks unaffected, see the security assessment in
go-in-lean-private `findings/AMD64-SBB-CARRYMASK-FLAGS/security-assessment.md`).
**Reported as golang/go#82825** (filed 2026-11-03 after maintainer approval; the issue
carries no fix, per the Gerrit workflow). **Mailed as Gerrit CL
https://go-review.googlesource.com/c/go/+/858262** (2026-11-03, Change-Id
`Ia4e6b5060246058a13505ef272b7090011bbeeec`, from the maintainer's MacBook checkout).
Ready-to-mail Gerrit CL package in `cl/` (fixedbugs regression test `issue82825.go` +
commit message `Fixes #82825.`, `fix.patch` includes the regenerated `ssaop/opGen.go`;
verification in `docs/cl-verification.md`).

## Reproducer (amd64)

```go
//go:noinline
func f(x, y uint64) uint64 {
	r := x << y
	eq := uint64(0)
	if y == 64 {
		eq = 1
	}
	return r + eq
}
// f(1, 65) is 1; the spec says 0 (1<<65 == 0, 65 != 64).
```

`-gcflags=-S` (go1.27.3) shows the `y == 64` test reading flags produced by the `SBBQ`
of the shift-bounds mask:

```
SHLQ  CX, AX
CMPQ  CX, $64     // v25: flags
SBBQ  DX, DX      // v12: mask of "y < 64" — SUBTRACTS, CLOBBERS the flags
SETEQ BL          // v28: the y == 64 test, intended to read v25
ANDQ  DX, AX
```

`SETEQ` after `SBBQ DX,DX` tests `!(y <u 64)`, i.e. `y >= 64`: for y = 65 the branch
assigns `eq = 1` (wrong); for y = 64 `SETEQ` happens to be right because SBBQ's zero flag
is set exactly when the mask is 0.

Variant sweep, all miscompiled on master `2b74366d` (amd64): `x << y` with `y == 64` or
`y != 64` (SETNE), `x >> y` unsigned with `y == 64`, `x >> y` signed with `y == 64`
(`rshS(-1, 65)` returns 0 instead of -1), and the 32-bit form `x << y` with `y == 32`.
Source order matters (`lshEqUseFirst`, `y < 64`): the scheduler usually, not always,
places the clobber between the producer and the other consumer.

## Reproducer (386, go1.27.3; not on master)

```go
//go:noinline
func d(x int16) int16 {
	r := int16(-2047) << uint64(uint64(x))
	if uint64(x) <= 8589934591 { // 0x1FFFFFFFF; false for negative x (uint64(x) >= 2^64-32768)
		r = int16(x) &^ 3
	}
	return r
}
// d(-1) is -4 on linux/386 with the constant visible to SSA (branch taken); the spec says 0.
```

Found by the cross-arch `--late` campaign (rel-386-branchy seed 85199; the RO-string
constant only becomes `Const64` in lower, past prove). The decomposed comparison
`(hi < 1) || (hi == 1 && lo <= 0xFFFFFFFF)` and the shift's count saturation share
`CMPLconst [1] hi`; the schedule puts `SBBLcarrymask` between the `CMPL` and the `SETEQ`,
so the compiled condition is the tautology `(hi == 0) | (hi >= 1)` and the branch is
always taken. The same program with the bound passed as a run-time parameter is correct.

## Cause

`AMD64Ops.go` (`SBBQcarrymask`, `SBBLcarrymask`) and `386Ops.go` (`SBBLcarrymask`) do not
set `clobberFlags: true`, although `SBB` is a subtraction and writes the flags register.
`flagalloc` therefore believes the flags of the feeding `CMP`/`TEST` stay live across the
mask and does not regenerate them for a second consumer (`SETcc`), which then reads the
`SBB`'s flags. The borrow-taking forms `SBBQ`/`SBBL`/`SBBLconst` are marked
`clobberFlags: true`; only the carry-mask forms are missing the annotation. This is the
same defect class as golang/go#81842 (ppc64 `DIV` clobbers CR0 unmarked) and
golang/go#21080 (s390x `MOVDaddr`), applied to x86.

## Fix (`fix.patch`, validated on master `2b74366d`)

Mark the three carry-mask ops `clobberFlags: true` (`go generate ./cmd/compile/internal/ssa`
after editing `_gen`). With the patch, the reproducers above print the spec values on
amd64 and 386, and `go test -short cmd/compile/internal/ssa cmd/compile/internal/ssacompile
cmd/compile/internal/test`, `go test cmd/internal/testdir -run 'Test/prove|Test/loopbce|
Test/checkbce|Test/codegen'` and `-run Test/fixedbugs` pass.

## Versions (2026-11-03, amd64, `f(1,65)`)

| Toolchain | result |
|---|---|
| go1.24.13, go1.25.5, go1.26.10, go1.27.3 | **wrong** (1) |
| master `2b74366d` (GOAMD64 v1/v2/v3) | **wrong** (1) |
| master + fix.patch | correct (0) |

## How it was found

Not by a theorem: the `--late` branchy cross campaign on 386 (seed 85199, go1.27.3,
S0=85000) reported six mismatches whose reduction led to the flag-clobbering schedule;
the amd64 form was then constructed by hand from the mechanism (the metamorphic fuzzer
does not compare a shift count against the shift width of the same value, so its amd64
campaigns had missed it). Minimization, disassembly and phase dumps (`-d=ssa/all/dump`)
localise the defect in the flag liveness annotation, not in a rewrite rule; the sibling
lint does not cover OpcodeTable fields.

## Post-hoc fuzzer mode (`--countvar`, 2026-11-03)

`metamorphic_fuzz.py --countvar --branchy` now makes the shift count the run-time variable
and adds a branch comparing it against a width-class constant with an all-constant phi
(`b := 0; if uint64(x) == K { b = 1 }`), which phiopt materialises as the second flag
consumer. On go1.27.3 amd64 it finds the family at ~3.5-3.7% of seeds (7/200 locally,
22/300 on the GEEKR9 native run) across all four widths and the `==`, `!=`, `>`, `<=`
operators — broader than the hand reproducer (`>` lowers to `CMPQconst [W] x`, sharing
the mask's flags directly). Every failing seed passes on master + fix.patch, i.e. the
whole family is covered by the single annotation fix.

## Known-issue search (2026-11-03)

No golang/go issue found for x86 carry masks clobbering flags (searched
"SBBQcarrymask clobberFlags", "SBBLcarrymask issue", "shift count == 64 miscompile",
"flagalloc SETEQ wrong"); golang/go#81842 is the same class on ppc64x, golang/go#21080 the
same class on s390x, golang/go#80399 is a carry-mask codegen regression without
correctness impact.

## Class sweep after the fix (2026-11-03)

`scripts/ops_clobber_lint.py` re-run against master 2b74366d + fix: after excluding
flag *producers* (CMP definitions, `<carry,result>` tuples — `Value.ClobbersFlags()`
already models those), pure flag *readers* (SETcc, CSEL/CSNEG, ARM ADC/SBC/RSC without
S, s390x LOCGR) and the flags-unaffected BMI2 shifts (SHLX/SHRX/SARX), the lint
reports **0 candidates on every backend**. All 114 pre-triage candidates were false
positives of the earlier lint version; the ARM `ADDSshift*`/`RSBSshift*`, 386
`ADDLcarry`/`SUBLcarry` and PPC64 `ANDCC` families are flag producers covered by the
tuple rule in `ClobbersFlags()`. The class is closed: the carry-mask ops of #82825
were the only unmarked flag writers reachable on master.
