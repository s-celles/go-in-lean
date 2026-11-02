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
func f() int {
	return bits.TrailingZeros64(uint64(uint16(bits.OnesCount16(16384))) &^ 16777217)
}

func main() {
	if got := f(); got != 64 {
		fmt.Printf("TrailingZeros64(0) = %d, want 64\n", got)
		panic("FAIL")
	}
}
