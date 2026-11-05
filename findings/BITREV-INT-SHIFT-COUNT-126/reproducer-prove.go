package main

import (
	"fmt"
	"math/bits"
)

// The divisor y is 85, never zero, yet go1.26 on arm64 and loong64 compiles
// f to an unconditional call to runtime.panicdivide.
//
//go:noinline
func f(x, y uint8) uint8 {
	return ^bits.Reverse8(y) | bits.RotateLeft8(x, 7)%y
}

func main() {
	fmt.Println(f(255, 85)) // want 85
}
