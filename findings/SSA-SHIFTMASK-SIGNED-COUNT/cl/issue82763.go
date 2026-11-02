// run

// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

import "fmt"

//go:noinline
func f(x int64) int64 { return ((x >> uint64(1<<63)) & 3) << 1 }

func main() {
	if got := f(-1); got != 6 {
		fmt.Printf("((x >> 1<<63) & 3) << 1 with x=-1 = %d, want 6\n", got)
		panic("FAIL")
	}
}
