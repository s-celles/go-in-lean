package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func f(x, y int16) int16 {
	return int16(func() uint64 { _, d := bits.Sub64(uint64((int8(bits.Reverse8(uint8(33))) / int8(-7))), uint64(x), uint64(uint8(y))); return d }())
}

func main() { fmt.Println("f(-1,1) =", f(-1, 1), "(want 1)") }
