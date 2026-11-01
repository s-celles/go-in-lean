// Execution tests for the SSA rewrite rules modelled in
// GoInLean/Compiler/GenericRules.lean. The compiler applies the rules when
// the divisor/multiplier is a constant, so each check compares a
// constant-operand expression (rewritten) against a variable-operand one
// (not rewritten, computed with a generic division) on boundary and random
// values. This is the same idea as cmd/compile/internal/test/divconst_test.go.
package tests

import (
	"math"
	"math/rand/v2"
	"testing"
)

//go:noinline
func divVar8(n, c int8) int8 { return n / c }

//go:noinline
func divuVar8(n, c uint8) uint8 { return n / c }

//go:noinline
func modVar64(n, c uint64) uint64 { return n % c }

//go:noinline
func divVar64(n, c int64) int64 { return n / c }

func TestCompilerPow2Rules(t *testing.T) {
	for x := 0; x < 256; x++ {
		n8 := int8(x)
		u8 := uint8(x)
		// Mul8/Div8u/Mod8u by 2^k, k < 7
		if n8*4 != n8<<2 || u8/8 != u8>>3 || u8%16 != u8&15 {
			t.Fatalf("8-bit pow2 rules differ at %d", x)
		}
		if divuVar8(u8, 32) != u8/32 {
			t.Fatalf("Div8u by 32: var %d const %d", divuVar8(u8, 32), u8/32)
		}
		// signed non-negative
		if n8 >= 0 && (n8/4 != int8(uint8(n8)>>2) || n8%4 != n8&3) {
			t.Fatalf("non-negative signed pow2 rules differ at %d", x)
		}
	}
	r := rand.New(rand.NewPCG(7, 8))
	for i := 0; i < 20000; i++ {
		u := r.Uint64()
		if u/32 != u>>5 || u%32 != u&31 || u/(1<<63) != u>>63 || u%(1<<63) != u&(1<<63-1) {
			t.Fatalf("64-bit unsigned pow2 rules differ at %#x", u)
		}
		if modVar64(u, 1<<5) != u%(1<<5) {
			t.Fatalf("Mod64u by 32: var vs const at %#x", u)
		}
		if u*64 != u<<6 {
			t.Fatalf("Mul64 pow2 differs at %#x", u)
		}
	}
}

func TestCompilerSignedDivPow2(t *testing.T) {
	// RULE-SDIV-POW2 at 8 bits, all n, k in 1..6; the 4-op sequence is the oracle.
	for x := 0; x < 256; x++ {
		n := int8(x)
		for k := 1; k < 7; k++ {
			seq := (n + int8(uint8(n>>7)>>(8-k))) >> k
			if divVar8(n, 1<<k) != seq {
				t.Fatalf("Div8 %d / %d: generic %d, sequence %d", n, 1<<k, divVar8(n, 1<<k), seq)
			}
		}
		// RULE-DIV-SPECIAL: x / -128 == (x & -x) >> 7 (as unsigned shift)
		if divVar8(n, math.MinInt8) != int8(uint8(n&-n)>>7) {
			t.Fatalf("Div8 by MinInt8 differs at %d", n)
		}
		// negative constant: n / -4 == -(n / 4)
		if n/-4 != -(n/4) || divVar8(n, -4) != -(n/4) {
			t.Fatalf("Div8 by -4 differs at %d", n)
		}
	}
	// 64 bits: compiled constant division vs the 4-op sequence and vs generic division
	r := rand.New(rand.NewPCG(9, 10))
	vals := []int64{0, 1, -1, 2, -2, math.MaxInt64, math.MinInt64, math.MinInt64 + 1, math.MaxInt64 - 1}
	for i := 0; i < 20000; i++ {
		vals = append(vals, int64(r.Uint64()))
	}
	for _, n := range vals {
		if n/32 != (n+int64(uint64(n>>63)>>(64-5)))>>5 || n/32 != divVar64(n, 32) {
			t.Fatalf("Div64 by 32 differs at %d", n)
		}
		if n/(1<<62) != (n+int64(uint64(n>>63)>>(64-62)))>>62 {
			t.Fatalf("Div64 by 2^62 differs at %d", n)
		}
		if divVar64(n, math.MinInt64) != int64(uint64(n&-n)>>63) {
			t.Fatalf("Div64 by MinInt64 differs at %d", n)
		}
	}
	// negative control from the Lean refutation: with k = 63 the sequence is wrong at MinInt64
	n := int64(math.MinInt64)
	seq63 := (n + int64(uint64(n>>63)>>(64-63))) >> 63
	if divVar64(n, math.MinInt64) == seq63 {
		t.Fatalf("expected the k=63 sequence to be wrong at MinInt64 (Lean counterexample), got equal %d", seq63)
	}
}

func TestCompilerShiftRules(t *testing.T) {
	for x := 0; x < 256; x++ {
		u := uint8(x)
		s := int8(x)
		for c := uint(0); c < 8; c++ {
			if (u>>c)<<c != u&(uint8(0xff)<<c) || (u<<c)>>c != u&(0xff>>c) {
				t.Fatalf("shift/mask rules differ at %d, c=%d", x, c)
			}
			for d := uint(0); d < 8; d++ {
				if (u<<c)<<d != u<<(c+d) || (u>>c)>>d != u>>(c+d) {
					t.Fatalf("shift composition differs at %d, c=%d d=%d", x, c, d)
				}
			}
		}
		if uint8(s>>7)>>7 != u>>7 {
			t.Fatalf("(Rsh8Ux64 (Rsh8x64 x _) 7) rule differs at %d", x)
		}
		var big uint = 64
		if uint64(u)<<big != 0 || uint64(u)>>big != 0 {
			t.Fatalf("shift by >= width is not 0 at %d", x)
		}
	}
}

// RULE-FOLD-RSHU-AUXINT / RULE-FOLD-RSHU-GO16: regression test of golang/go#15175
// (fixed in Go 1.7): unsigned shift of a constant with the top bit set, then compare.
func TestIssue15175Regression(t *testing.T) {
	var a6 uint8 = 253
	if a6>>0 != 253 || !(a6>>0 == 253) {
		t.Fatalf("issue 15175 regression: uint8(253)>>0 = %d", a6>>0)
	}
	// the Lean refutation witness, as a constant-folded expression
	const c uint8 = 253
	if x := c >> 0; x != 253 || int8(x) != -3 {
		t.Fatalf("constant folding of uint8(253)>>0 gave %d", x)
	}
}
