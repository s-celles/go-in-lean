# ARM-SUB64-BORROWOUT: bits.Sub64 returns a wrong borrow on GOARCH=arm

**Classification:** `go_discrepancy_reproduced`. **Compiler miscompilation (wrong code),
GOARCH=arm (32-bit), GOARM=5 and default.** Plain safe Go code calls `math/bits.Sub64`
with in-contract inputs and gets a wrong `borrowOut` output (0 instead of 1); the `diff`
output is correct. No memory-safety impact: wrong values only. `bits.Sub64` feeds
multi-word subtraction (`math/big`, `crypto`), so results can be silently wrong on 32-bit
ARM.
**Affected:** go1.21.13 through go1.27.3 and master `2b74366d` (go1.15+ era not tested;
go1.21.13 already wrong). Correct on amd64, 386 and mipsle.
**Human review status:** reviewed and filed as golang/go#82834 on 2026-11-03 (maintainer approval).

## Reproducer

```go
package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func f(x, y int16) int16 {
	return int16(func() uint64 {
		_, d := bits.Sub64(uint64((int8(bits.Reverse8(uint8(33))) / int8(-7))), uint64(x), uint64(uint8(y)))
		return d
	}())
}

func main() { fmt.Println("f(-1,1) =", f(-1, 1), "(want 1)") }
// GOARCH=arm (linux/arm under qemu-arm, GOARM=5 or default), go1.21.13..go1.27.3, master:
// prints 0.  amd64, 386, mipsle print 1.
```

`x=-1` makes the subtrahend `uint64(int16(-1)) = 0xFFFFFFFFFFFFFFFF` (a sign extension
with high half all ones); the minuend is 17 (the `int8` division is a non-constant
expression the frontend cannot fold); the borrow input is `uint64(uint8(1)) = 1`, inside
the documented 0-or-1 contract. Per the `Sub64` contract the borrow output is 1.

Minimisation is non-monotone: replacing the division expression with the literal `17`,
or passing the subtrahend as a plain `uint64` parameter instead of the sign-extended
`int16`, makes the bug disappear - the trigger is the combination of a constant-folded
minuend with a sign-extension-derived subtrahend in the 64-bit decomposition.

## Assembly (go1.27.3, linux/arm)

```
MOVH  x(FP), R0          ; R0 = uint16(x), zero-extended
MOVH  y+2(FP), R1        ; R1 = y
MOVBU R1@>0, R1          ; R1 = uint8(y)  (borrow-in)
SRA   $31, R0, R2        ; R2 = high half of the subtrahend's 64-bit value
MOVW  $17, R3            ; minuend (constant-folded)
SUB.S R0, R3, R3         ; low subtract, sets carry
RSC   $0, R2, R2         ; high subtract with borrow
SUB.S R1, R3, R1         ; subtract the borrow-in, sets carry
SBC   $0, R2, R1         ; propagate
BIC   R0->31, R1, R0     ; borrow extraction (bit formula)
SRL   $31, R0, R0        ; >> 31 -> borrowOut
```

The `diff` output of the same call is correct, so the SUB.S/RSC/SBC difference chain is
right; the wrong value comes from the borrow-extraction tail (`BIC`/`SRL` implementing
`((^x & y) | (^(x^y) & diff)) >> 63` at the high half), which consumes `R0` - the
zero-extended low half of the subtrahend - through a rotated operand where the formula
needs the sign-extension-derived high-half operand. The precise faulty rewrite rule is
not yet isolated (candidates: the ARM lowering of the `Sub64borrow` borrow-output at
`ARM.rules`, the `SUBSshift*`/`RSBSshift*` family - also the unmarked-flag candidates
of `scripts/ops_clobber_lint.py`).

## Versions (2026-11-03, linux/arm under qemu-arm 11.1.2)

| Toolchain | f(-1,1) |
|---|---|
| go1.21.13, go1.24.13, go1.25.5, go1.26.10, go1.27.3 | **wrong** (0) |
| master `2b74366d` (GOARM default and GOARM=5) | **wrong** (0) |
| same program on amd64, 386, mipsle | correct (1) |

## How it was found

The new `--carry` mode of `scripts/metamorphic_fuzz.py` (bits.Add64/Sub64 tuples mixed
with comparisons), campaign `carrycross` on GEEKR9: seed 997146, `rel-arm-branchy`
(go1.27.3), expr 153. Found organically by the fuzzer; reduced by hand; the differential
harness (constant vs run-time minuend) isolated the wrong side.

## Known-issue search (2026-11-03)

No golang/go issue found for a wrong `bits.Sub64` borrow on 32-bit ARM (searched
"bits.Sub64 borrow wrong arm", "Sub64borrow arm", "arm RSC SBC carry"); the closest are
golang/go#80399 (amd64 carry folding, performance), golang/go#79887 (amd64 InvertFlags
ICE) and golang/go#82786 (ARM MVNshiftRA, a different ARM constant-fold defect).
