// Package reference holds deliberately faulty re-implementations of the
// math/bits functions ("mutants"). They exist only to demonstrate that the
// pipeline detects defects: each mutant has a Lean twin in
// mutants/*.lean whose proof attempt must FAIL with a counterexample, and
// that counterexample must make the Go mutant below disagree with the real
// math/bits function, while the real function keeps passing.
//
// Nothing in this package is used by anything other than tests.
package reference

import "math/bits"

// Add64WrongCarry drops the `(x|y) &^ sum` term of the carry formula, so a
// carry produced by the low bits propagating into the top bit is lost.
func Add64WrongCarry(x, y, carry uint64) (sum, carryOut uint64) {
	sum = x + y + carry
	carryOut = (x & y) >> 63
	return
}

// OnesCount64WrongMask uses the wrong mask in the second SWAR step (0x3333…
// becomes 0x3333…3332), so a particular bit is never counted.
func OnesCount64WrongMask(x uint64) int {
	const m0 = 0x5555555555555555
	const m1 = 0x3333333333333332
	const m2 = 0x0f0f0f0f0f0f0f0f
	x = x>>1&m0 + x&m0
	x = x>>2&m1 + x&m1
	x = (x>>4 + x) & m2
	x += x >> 8
	x += x >> 16
	x += x >> 32
	return int(x) & (1<<7 - 1)
}

// RotateLeft64OffByOne masks the rotation count with 0x1f instead of 0x3f,
// which is correct for all k in [0,32) and wrong otherwise.
func RotateLeft64OffByOne(x uint64, k int) uint64 {
	const n = 64
	s := uint(k) & (n/2 - 1)
	return x<<s | x>>(n-s)
}

// Len64NoHighHalf forgets the first `if x >= 1<<32` step.
func Len64NoHighHalf(x uint64) (n int) {
	if x >= 1<<16 {
		x >>= 16
		n += 16
	}
	if x >= 1<<8 {
		x >>= 8
		n += 8
	}
	return n + bits.Len8(uint8(x))
}

// TrailingZeros64WrongShift uses a 5-bit instead of 6-bit de Bruijn index.
func TrailingZeros64WrongShift(x uint64) int {
	if x == 0 {
		return 64
	}
	const deBruijn64 = 0x03f79d71b4ca8b09
	return int(deBruijn64tab[(x&-x)*deBruijn64>>(64-5)&63])
}

var deBruijn64tab = [64]byte{
	0, 1, 56, 2, 57, 49, 28, 3, 61, 58, 42, 50, 38, 29, 17, 4,
	62, 47, 59, 36, 45, 43, 51, 22, 53, 39, 33, 30, 24, 18, 12, 5,
	63, 55, 48, 27, 60, 41, 37, 16, 46, 35, 44, 21, 52, 32, 23, 11,
	54, 26, 40, 15, 34, 20, 31, 10, 25, 14, 19, 9, 13, 8, 7, 6,
}
