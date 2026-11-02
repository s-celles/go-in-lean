// run

// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package main

var sink int

//go:noinline
func f(x uint8) {
	// int16(x)-513 is in [-513, -258], so this is always false.
	if int32(int16(x)-513) < -536870911 {
		sink = 1
	}
}

func main() {
	for _, x := range []uint8{0, 1, 128, 255} {
		f(x)
		if sink != 0 {
			panic("FAIL: branch taken")
		}
	}
}
