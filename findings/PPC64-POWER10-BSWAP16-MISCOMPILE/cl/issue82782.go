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
func f(k uint16, y, z int16) int16 {
	r := ^int16(bits.ReverseBytes16(k))
	if y <= z {
		r = 7
	}
	return r
}

func main() {
	if got := f(0x0400, 5, 1); got != -5 {
		fmt.Printf("f(0x0400, 5, 1) = %d, want -5\n", got)
		panic("FAIL")
	}
}
