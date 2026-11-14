// run

// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func reverseBytes16(x uint16) uint16 {
	return bits.ReverseBytes16(x)
}

//go:noinline
func f(k uint16, y, z int16) int16 {
	r := ^int16(bits.ReverseBytes16(k))
	if y <= z {
		r = 7
	}
	return r
}

func main() {
	for x := uint32(0); x < 1<<16; x++ {
		want := uint16(x<<8 | x>>8)
		if got := reverseBytes16(uint16(x)); got != want {
			fmt.Printf("ReverseBytes16(%#04x) = %#04x, want %#04x\n", x, got, want)
			panic("FAIL")
		}
	}

	if got := f(0x0400, 5, 1); got != -5 {
		fmt.Printf("f(0x0400, 5, 1) = %d, want -5\n", got)
		panic("FAIL")
	}
}
