package main

import (
	"fmt"
	"math/bits"
)

// For y = 255, y|128 = 255 and bits.Reverse8(255) = 255, so the condition is
// false and f returns 0. go1.26.10 on arm64 (and loong64) returns 1: prove
// reports "Proved Neq8" because the BitRev8 intrinsic is typed int.
//
//go:noinline
func f(y uint8) int {
	if bits.Reverse8(y|128) != 255 {
		return 1
	}
	return 0
}

func main() { fmt.Println(f(255)) } // want 0
