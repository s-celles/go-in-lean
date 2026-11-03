<!-- Filed as golang/go#82834 on 2026-11-03 after maintainer approval. -->

### What version of Go are you using (`go version`)?

go1.21.13 through go1.27.3 and master (go1.28-devel_2b74366d).

### Output of `go env` in your module/workspace:

GOARCH=arm (linux/arm; reproduced under qemu-arm with GOARM unset and with GOARM=5).

### What did you do?

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
```

### What did you see happen?

On GOARCH=arm the program prints `0`. On amd64, 386 and mipsle it prints `1`.

### What did you expect to see?

`1`. `uint64(int16(-1)) = 0xFFFFFFFFFFFFFFFF`, the minuend is 17 and the borrow input is
`uint64(uint8(1)) = 1`, inside the documented 0-or-1 contract, so `bits.Sub64` must
report a borrow. The `diff` output of the same call is correct (17); only the `borrowOut`
output is wrong.

### Analysis

The 64-bit subtraction is decomposed into 32-bit halves (`SUB.S`/`RSC`/`SBC`), which
compute the correct difference; the wrong value comes from the borrow-extraction tail
that implements `borrowOut = ((^x & y) | (^(x^y) & diff)) >> 63`. The reproducer needs
the combination of a constant-folded minuend (`MOVW $17`) with a subtrahend whose high
half comes from the sign extension of a narrow value (`uint64(int16(x))`, `SRA $31`):
replacing the division expression with the literal `17`, or passing the subtrahend as a
plain `uint64` parameter, makes the bug disappear, so a rewrite that matches the
extraction against a specific producer shape is the likely cause.

`bits.Sub64` is a building block of multi-word arithmetic (`math/big`); a wrong borrow is
a silent wrong result on 32-bit ARM.

Disassembly of `f` (go1.27.3, linux/arm):

```
MOVH  x(FP), R0
MOVH  y+2(FP), R1
MOVBU R1@>0, R1
SRA   $31, R0, R2
MOVW  $17, R3
SUB.S R0, R3, R3
RSC   $0, R2, R2
SUB.S R1, R3, R1
SBC   $0, R2, R1
BIC   R0->31, R1, R0
SRL   $31, R0, R0
```

Found with a metamorphic differential fuzzer (constant vs run-time operands) over
`bits.Add64`/`bits.Sub64` tuples.

Assisted by AI.
