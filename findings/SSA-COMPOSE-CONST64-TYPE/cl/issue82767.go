// run

// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "fmt"

//go:noinline
func f(y int32) int32 { return (y >> 1) >> (uint64(1) << 62) }

func main() {
	if got := f(2); got != 0 {
		fmt.Printf("(int32(2) >> 1) >> (1<<62) = %d, want 0\n", got)
		panic("FAIL")
	}
}
