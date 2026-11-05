package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func f(x, y uint64) uint64 { return x << bits.Reverse64(y) }

//go:noinline
func g(x uint64, y uint) uint64 { return x >> bits.Reverse(y) }

func main() {
	// Reverse64(3) = 0xC000000000000000, an unsigned count >= 64: want 0 0
	fmt.Println(f(3, 3), g(3, 3))
}
