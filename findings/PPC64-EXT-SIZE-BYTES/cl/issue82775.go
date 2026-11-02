// run

// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "fmt"

//go:noinline
func f(x int32) int32 { return int32(int16(x >> 1)) }

func main() {
	if got := f(-1 << 31); got != 0 {
		fmt.Printf("int32(int16((-1<<31)>>1)) = %d, want 0\n", got)
		panic("FAIL")
	}
}
