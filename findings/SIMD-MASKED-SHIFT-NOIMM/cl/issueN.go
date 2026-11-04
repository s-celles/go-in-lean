// run

//go:build goexperiment.simd && amd64

// Copyright 2026 The Go Authors. All rights reserved.
// Use of this source code is governed by a BSD
// license that can be found in the LICENSE file.

package main

import "simd"

// IfElse of a constant shift fuses the shift into a merge-masked EVEX
// instruction (...MaskedNNNconstMerging); the code generator used to drop
// the shift count, so the 512-bit variant failed to assemble.

//go:noinline
func f(x, y simd.Uint64s, m simd.Mask64s) simd.Uint64s {
	return x.ShiftAllLeft(2).IfElse(m, y)
}

func main() {
	var s [64]uint64
	x := simd.BroadcastUint64s(uint64(3))
	y := simd.BroadcastUint64s(uint64(9))

	m := x.Greater(simd.BroadcastUint64s(uint64(2))) // all lanes true
	f(x, y, m).Store(s[:])
	if s[0] != 12 || s[1] != 12 {
		panic("bad masked shift: true lanes must be x<<2")
	}

	m2 := x.Less(simd.BroadcastUint64s(uint64(2))) // all lanes false
	f(x, y, m2).Store(s[:])
	if s[0] != 9 || s[1] != 9 {
		panic("bad masked shift: false lanes must keep y")
	}
}
