<!-- Posted on golang/go#80577 on 2026-11-02 after human approval: https://github.com/golang/go/issues/80577#issuecomment-6588709343 -->
A ppc64/ppc64le instance of the same contract problem, which the riscv64-specific CL 806340 does
not cover. Reproduces with go1.27.3 and master on ppc64le (power8, power9) and ppc64; amd64, arm64,
riscv64 and s390x are correct.

```go
package main

import (
	"fmt"
	"math/bits"
)

var tab256 [256]int8

//go:noinline
func v174(x, y int8, k0 int32, k1 uint16, k2 uint8, k3 int8, k4 int64, k5 uint64, k6 uint64, k7 uint16, k8 int16) int8 { return func() (r int8) { defer func() { if recover() != nil { r = int8(0x5A) } }(); return int8(tab256[int(uint(func() int8 { r := int8(((uint8(int32(x)) << uint64(uint16(x))) + uint8(bits.RotateLeft8(uint8(y), int(int8(y)))))); if int16(uint16(y)) >= k8 { r = (int8((int64(y) >> k5)) << k6) }; return r }()) & 255)]) }() }

func main() {
	for i := range tab256 {
		tab256[i] = int8(i*7 + 1)
	}
	fmt.Println(v174(0, -1, int32(-268435455), uint16(8), uint8(127), int8(-1), int64(-65535), uint64(18446744073709551615), uint64(18446744073709551615), uint16(8193), int16(9))) // want -6, ppc64 prints 1
}
```

`int16(uint16(y))` keeps type `uint16` while its register holds the sign-extended `EXTSB y`, so the
`MOVHreg` before the signed compare is elided. It is live across the `RotateLeft8` call and gets
spilled and restored by type:

```
EXTSB R4,R7
MOVH  R7,58(R1)
CALL  math/bits.RotateLeft8(SB)
MOVHZ 58(R1),R7      // zero-extending restore: 65535 instead of -1
CMPW  R6,R7          // signed compare with k8 = 9
```

As in #81928, whether a program hits it depends on scheduling: the function has to stay on one line
here; split across lines it is scheduled differently and no longer spills that value.

Found with a metamorphic fuzzer under qemu.

Assisted by AI.
