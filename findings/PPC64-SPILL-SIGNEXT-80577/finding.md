# PPC64-SPILL-SIGNEXT-80577: ppc64 instance of golang/go#80577 (restore extension chosen from type)

**Classification:** `known_issue`: a ppc64/ppc64le manifestation of the open golang/go#80577
("regalloc uses unreliable type data (like `v.Type.IsSigned()`) to choose the restore of spills"),
which was opened for riscv64. The riscv64-specific fix (CL 806340) does not cover ppc64.
**Impact:** silent wrong results (a signed comparison evaluated on a zero-extended value).
**Affected:** `GOARCH=ppc64le` (power8, power9) and `ppc64`, go1.27.3 and master `babb75be`.
amd64, arm64, riscv64 and s390x run the same program correctly.
**Human review status:** approved 2026-11-02; posted as a comment on golang/go#80577 (https://github.com/golang/go/issues/80577#issuecomment-6588709343).

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
