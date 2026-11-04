package main

import "simd"

//go:noinline
func f(x, y simd.Uint64s, m simd.Mask64s) simd.Uint64s {
	return x.ShiftAllLeft(2).IfElse(m, y)
}

func main() {}
