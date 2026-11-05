# PPC64-SPILL-SIGNEXT-80577: ppc64 instance of golang/go#80577 (restore extension chosen from type)

**Classification:** `known_issue`: a ppc64/ppc64le manifestation of the open golang/go#80577
("regalloc uses unreliable type data (like `v.Type.IsSigned()`) to choose the restore of spills"),
which was opened for riscv64. The riscv64-specific fix (CL 806340) does not cover ppc64.
**Impact:** silent wrong results (a signed comparison evaluated on a zero-extended value).
**Affected:** `GOARCH=arm64`, `ppc64le` and `ppc64`, from at least go1.21.13 through
go1.27.3 and master `ede4e4ff00`. amd64, 386, arm, mipsle, mips64le, riscv64, s390x
and loong64 run the minimal program correctly.
**Human review status:** approved 2026-11-02; initial comment posted on golang/go#80577
(https://github.com/golang/go/issues/80577#issuecomment-6588709343). Minimal arm64/ppc64
follow-up approved and posted 2026-11-04
(https://github.com/golang/go/issues/80577#issuecomment-6643325028).

## What happens

`int16(uint16(y))` with `y int8` keeps the SSA type `uint16`, but its register holds `EXTSB(y)`,
already sign-extended, so the `MOVHreg` before the signed 16-bit comparison is elided. The value is
live across a call (`math/bits.RotateLeft8`), so regalloc spills it with a 2-byte store and restores
it with a **zero-extending** load chosen from the unsigned type:

```
EXTSB R4,R7            ; int16(uint16(int8 y)) = -1, sign-extended in the register
MOVH  R7,58(R1)        ; spill (2 bytes)
CALL  math/bits.RotateLeft8(SB)
MOVHZ 58(R1),R7        ; restore with zero-extension: 65535 instead of -1
CMPW  R6,R7            ; signed compare against k8 = 9 -> branch wrongly taken
```

This is exactly the contract described in #80577: a spill stores the low `t.Size()` bytes and the
restore re-extends according to `t` alone, so eliding an extension on a value whose type disagrees
with its register contents is unsound across a spill.

## Reproducer (`reproducer.go`)

`v174(0, -1, ...)` prints `RESULT=1`; the correct value is `-6`. The function body must stay on a
single line: the same function split across lines is scheduled differently (the scheduler breaks
ties by source position), the value is not spilled, and the result is correct. Whether a program
hits the defect depends on scheduling and register pressure, as #81928 also notes.

## Addendum (2026-11-04): minimal repro, arm64, and a second width

`minimal_reproducer.go` removes the closure, `defer`, table, intrinsics, source-position
sensitivity and artificial register pressure:

```go
//go:noinline
func id(x int64) int64 { return x }

//go:noinline
func f(y int8) int64 {
	v := int16(uint16(y))
	z := id(int64(v))
	if v >= 9 { return z + 1000 }
	return z - 1000
}
```

`f(-1)` must return `-1001`, but returns `999` on arm64, ppc64le and ppc64. On
arm64 the decisive sequence is `SXTB`, a 2-byte `MOVH` spill, `CALL`, then the
zero-extending `MOVHU` restore before the signed `CMPW`. PPC64 uses the analogous
`EXTSB`, `MOVH`, `MOVHZ` sequence. The call alone makes the value live across a
spill; no extra pressure is required.

`scripts/spill_restore_fuzz.py` varies the source width, value width, and 0–20
additional live call arguments. On current tip:

| Target | Mismatches | Extents |
|---|---:|---|
| ppc64le / ppc64 | 42/84 each | every pressure for 8→16 and 16→32 |
| riscv64 | 0/84 | clean control |
| arm64 | 1/4 at pressure 0 | 8→16 |
| 386, arm, mipsle, mips64le, s390x, loong64 | 0/4 each | clean controls |

The 16→32 ppc64 form is `int32(uint32(int16(-1)))`; after the call it is restored
as 4294967295 instead of -1. Both minimal widths fail on ppc64le with every tested
toolchain from go1.21.13 through go1.27.3 and current tip. The arm64 8→16 case has
the same version range. This is a broader manifestation of #80577, not a new root
cause; the follow-up was posted on #80577 after human review.

### ARM64 rule and experimental guard

Before late lowering the signed comparison has `MOVHreg <int32> v8`, where
`v8 = MOVBreg <uint16> y`. `ARM64latelower.rules` folds
`MOVHreg x:(MOVBreg _)` to `MOVDreg x` unconditionally. That is valid while `x`
stays in a register, but not after a spill: `x`'s `uint16` type selects `MOVHU`
for its restore.

`arm64-experiment.patch` guards all six signed-over-signed double-extension
folds with `x.Type.Size() == 8 || x.Type.IsSigned()`. On `ede4e4ff00` it changes
the minimal arm64 result from `999` to `-1001`, makes all 84 width/pressure cases
clean, and passes:

```text
go test cmd/compile/internal/ssa cmd/compile/internal/ssacompile cmd/compile/internal/test
```

This is a local validation of the missing restore condition, not proposed as the
final upstream design: #80577 already tracks expressing the spill/restore contract
centrally, which can supersede architecture-local guards.

## Addendum (2026-11-05): producer audit and PPC64 rule guards

The audit mode of `scripts/spill_restore_fuzz.py` now covers all widening pairs
among 8, 16, 32 and 64 bits, both extension directions, eight producer families
(argument, load, noinline call, signed shift, multiplication, Phi, rotate and
reverse-bytes), and pressure 0–20. The semantic control is the same program
compiled for amd64.

On pristine tip `672197524bb0`, every failing shape is stable at all 21 pressure
levels:

| Target | Signed-chain mismatches | Failing shapes |
|---|---:|---|
| arm64 | 105/945 | 8→16 from arg, load, call, multiply and Phi |
| ppc64le | 441/945 | 8→16 and 8/16→32 across 21 producer/width groups |
| ppc64 | 21/45 at pressure 0 | same groups as ppc64le |
| 386, arm, mipsle, mips64le, riscv64, s390x, loong64 | 0/45 each at pressure 0 | clean controls |

The symmetric zero-extension direction is 0/45 on arm64, ppc64le and ppc64.
The new PPC64 failures include `RotateLeft8/16` and `ReverseBytes16`; disassembly
still shows the same contract violation (`EXTSB`/`EXTSH`, narrow spill, then
`MOVHZ`/`MOVWZ` restore), not a second root cause.

The responsible PPC64 folds are the unguarded repeated-extension rules around
`PPC64.rules:669`, `:691` and `:697`. `ppc64-experiment.patch` guards the signed
folds when the inner value's type would not reproduce its sign bits after a
restore. Together with `arm64-experiment.patch`, it makes all 945 signed-chain
cases clean on arm64 and ppc64le and all 45 pressure-zero cases clean on ppc64.

[CL 825904 patchset 6](https://go-review.googlesource.com/c/go/+/825904)
introduces the central `SpillKeepsZeroBits` and `SpillKeepsSignBits` predicates
and remains in review. Source inspection shows that patchset 6 does not apply
them to the ARM64 double-extension or PPC64 repeated-extension rules above, so
it does not yet cover these manifestations. The local guards validate the
missing condition; a final upstream change should use those central predicates
rather than retain architecture-local spellings. The guarded compiler also
passes the targeted SSA compiler test suites:

```text
go test cmd/compile/internal/ssa cmd/compile/internal/ssacompile cmd/compile/internal/test
```

## Versions (2026-11-02, qemu-ppc64le/qemu-ppc64 11.1.2)

| Toolchain | power8 | power9 | ppc64 (BE) |
|---|---|---|---|
| go1.27.3 | wrong | wrong | wrong |
| master `babb75be` | wrong | wrong | |
| go1.21.13, go1.23.12, go1.24.1 | correct for this program | | |

The go1.24.2 point release changed closure inlining (`c2a34bedee`, `0ace2d8aca`); that changed the
schedule of the fuzz program and exposed the defect, but the defect itself is the spill/restore
contract, not those changes.

## How it was found

`--bits` index campaign on master, ppc64le `GOPPC64=power9`, seed 61164; reduced on the target with
an automatic delta reducer (`build/reduce_p9.py`) and confirmed with `go tool objdump`.
