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
	fmt.Println("RESULT=" + fmt.Sprint(v174(0, -1, int32(-268435455), uint16(8), uint8(127), int8(-1), int64(-65535), uint64(18446744073709551615), uint64(18446744073709551615), uint16(8193), int16(9))) + " (want -6)")
}
