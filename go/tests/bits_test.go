// Property tests for math/bits that mirror the Lean specifications in
// GoInLean/Properties/Bits.lean. They run against the *real* standard
// library of the pinned toolchain and act as the independent oracle:
// boundary values, exhaustive 8/16-bit checks, and fuzzing with math/big as
// reference. Each test names the property id from targets/properties.yaml.
package tests

import (
	"math/big"
	"math/bits"
	"testing"
)

var boundary64 = []uint64{0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x100, 0xffff, 0x10000, 0x7fffffff, 0x80000000,
	0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000, 0xffffffffffffffff, 0xfffffffffffffffe,
	0x5555555555555555, 0xaaaaaaaaaaaaaaaa, 0x0123456789abcdef}

func init() {
	for i := 0; i < 64; i++ {
		boundary64 = append(boundary64, 1<<i, ^(uint64(1) << i))
	}
}

// naive oracles (bit-by-bit, mirroring GoInLean.Semantics.BitSpec)
func lenSpec(x uint64, w int) int {
	n := 0
	for i := 0; i < w; i++ {
		if x>>i&1 == 1 {
			n = i + 1
		}
	}
	return n
}
func ctzSpec(x uint64, w int) int {
	for i := 0; i < w; i++ {
		if x>>i&1 == 1 {
			return i
		}
	}
	return w
}
func popSpec(x uint64, w int) int {
	n := 0
	for i := 0; i < w; i++ {
		n += int(x >> i & 1)
	}
	return n
}
func revSpec(x uint64, w int) uint64 {
	var r uint64
	for i := 0; i < w; i++ {
		if x>>(w-1-i)&1 == 1 {
			r |= 1 << i
		}
	}
	return r
}

// BITS-LEN-8 .. BITS-POP-16 .. BITS-REV-16: exhaustive at 8 and 16 bits.
func TestExhaustive8and16(t *testing.T) {
	for x := 0; x < 1<<16; x++ {
		x16 := uint16(x)
		if int(bits.Len16(x16)) != lenSpec(uint64(x), 16) {
			t.Fatalf("Len16(%#x)", x)
		}
		if bits.TrailingZeros16(x16) != ctzSpec(uint64(x), 16) {
			t.Fatalf("TrailingZeros16(%#x)", x)
		}
		if bits.OnesCount16(x16) != popSpec(uint64(x), 16) {
			t.Fatalf("OnesCount16(%#x)", x)
		}
		if uint64(bits.Reverse16(x16)) != revSpec(uint64(x), 16) {
			t.Fatalf("Reverse16(%#x)", x)
		}
		if bits.ReverseBytes16(x16) != x16>>8|x16<<8 {
			t.Fatalf("ReverseBytes16(%#x)", x)
		}
		if x < 256 {
			x8 := uint8(x)
			if bits.Len8(x8) != lenSpec(uint64(x), 8) || bits.TrailingZeros8(x8) != ctzSpec(uint64(x), 8) ||
				bits.OnesCount8(x8) != popSpec(uint64(x), 8) || uint64(bits.Reverse8(x8)) != revSpec(uint64(x), 8) {
				t.Fatalf("8-bit mismatch at %#x", x)
			}
		}
	}
}

// BITS-LEN-64, BITS-LZ-64, BITS-TZ-64, BITS-POP-64, BITS-REV-64 on boundary values.
func TestBoundary64(t *testing.T) {
	for _, x := range boundary64 {
		if bits.Len64(x) != lenSpec(x, 64) {
			t.Errorf("Len64(%#x) = %d", x, bits.Len64(x))
		}
		if bits.LeadingZeros64(x) != 64-lenSpec(x, 64) {
			t.Errorf("LeadingZeros64(%#x)", x)
		}
		if bits.TrailingZeros64(x) != ctzSpec(x, 64) {
			t.Errorf("TrailingZeros64(%#x)", x)
		}
		if bits.OnesCount64(x) != popSpec(x, 64) {
			t.Errorf("OnesCount64(%#x)", x)
		}
		if bits.Reverse64(x) != revSpec(x, 64) {
			t.Errorf("Reverse64(%#x)", x)
		}
		x32 := uint32(x)
		if bits.Len32(x32) != lenSpec(uint64(x32), 32) || bits.TrailingZeros32(x32) != ctzSpec(uint64(x32), 32) ||
			bits.OnesCount32(x32) != popSpec(uint64(x32), 32) || uint64(bits.Reverse32(x32)) != revSpec(uint64(x32), 32) {
			t.Errorf("32-bit mismatch at %#x", x32)
		}
	}
}

// BITS-ROTL-64 / BITS-ROTL-NEG-64: rotation by k mod 64; negative k rotates right.
func rotlSpec(x uint64, k int) uint64 {
	r := ((k % 64) + 64) % 64
	var out uint64
	for i := 0; i < 64; i++ {
		if x>>i&1 == 1 {
			out |= 1 << ((i + r) % 64)
		}
	}
	return out
}

func TestRotateLeft(t *testing.T) {
	for _, x := range boundary64 {
		for _, k := range []int{0, 1, 31, 32, 33, 63, 64, 65, -1, -63, -64, -65, 1 << 40, -(1 << 40)} {
			if bits.RotateLeft64(x, k) != rotlSpec(x, k) {
				t.Errorf("RotateLeft64(%#x, %d)", x, k)
			}
			if bits.RotateLeft64(x, -k) != bits.RotateLeft64(x, 64-(k%64)) {
				t.Errorf("RotateLeft64(%#x, -%d) is not rotate right", x, k)
			}
		}
	}
}

// BITS-ADD-64 / BITS-SUB-64 / BITS-MUL-64 / BITS-DIV-64 with math/big as oracle.
func bigU64(x uint64) *big.Int { return new(big.Int).SetUint64(x) }

var two64 = new(big.Int).Lsh(big.NewInt(1), 64)

func checkAddSubMulDiv(t *testing.T, x, y uint64) {
	t.Helper()
	for _, c := range []uint64{0, 1} {
		s, co := bits.Add64(x, y, c)
		want := new(big.Int).Add(bigU64(x), bigU64(y))
		want.Add(want, bigU64(c))
		got := new(big.Int).Lsh(bigU64(co), 64)
		got.Or(got, bigU64(s))
		if want.Cmp(got) != 0 || co > 1 {
			t.Errorf("Add64(%#x,%#x,%d) = (%#x,%#x)", x, y, c, s, co)
		}
		d, bo := bits.Sub64(x, y, c)
		// x = y + c + d - bo<<64
		rhs := new(big.Int).Add(bigU64(y), bigU64(c))
		rhs.Add(rhs, bigU64(d))
		rhs.Sub(rhs, new(big.Int).Lsh(bigU64(bo), 64))
		if rhs.Cmp(bigU64(x)) != 0 || bo > 1 {
			t.Errorf("Sub64(%#x,%#x,%d) = (%#x,%#x)", x, y, c, d, bo)
		}
	}
	hi, lo := bits.Mul64(x, y)
	prod := new(big.Int).Mul(bigU64(x), bigU64(y))
	got := new(big.Int).Lsh(bigU64(hi), 64)
	got.Or(got, bigU64(lo))
	if prod.Cmp(got) != 0 {
		t.Errorf("Mul64(%#x,%#x) = (%#x,%#x)", x, y, hi, lo)
	}
	// Div64(hi, lo, y) for hi < y, y != 0
	if y != 0 {
		for _, h := range []uint64{0, y - 1, y / 2, x % y} {
			z := new(big.Int).Lsh(bigU64(h), 64)
			z.Or(z, bigU64(lo))
			q, r := bits.Div64(h, lo, y)
			wq, wr := new(big.Int).QuoRem(z, bigU64(y), new(big.Int))
			if !wq.IsUint64() || wq.Uint64() != q || wr.Uint64() != r {
				t.Errorf("Div64(%#x,%#x,%#x) = (%#x,%#x), want (%s,%s)", h, lo, y, q, r, wq, wr)
			}
			if rr := bits.Rem64(x, lo, y); rr != new(big.Int).Mod(new(big.Int).Or(new(big.Int).Lsh(bigU64(x), 64), bigU64(lo)), bigU64(y)).Uint64() {
				t.Errorf("Rem64(%#x,%#x,%#x) = %#x", x, lo, y, rr)
			}
		}
	}
}

func TestAddSubMulDivBoundary(t *testing.T) {
	for _, x := range boundary64 {
		for _, y := range boundary64 {
			checkAddSubMulDiv(t, x, y)
		}
	}
}

func FuzzAddSubMulDiv(f *testing.F) {
	f.Add(uint64(0), uint64(0))
	f.Add(^uint64(0), ^uint64(0))
	f.Add(uint64(1)<<63, uint64(3))
	f.Fuzz(func(t *testing.T, x, y uint64) { checkAddSubMulDiv(t, x, y) })
}

// BITS-DIV-PANIC-64: Div64 panics iff y == 0 (divide) or y <= hi (overflow).
func TestDiv64Panics(t *testing.T) {
	mustPanic := func(hi, lo, y uint64, want string) {
		t.Helper()
		defer func() {
			e := recover()
			if e == nil {
				t.Errorf("Div64(%#x,%#x,%#x) did not panic", hi, lo, y)
				return
			}
			if s, ok := e.(error); !ok || s.Error() != want {
				t.Errorf("Div64(%#x,%#x,%#x) panicked with %v, want %q", hi, lo, y, e, want)
			}
		}()
		bits.Div64(hi, lo, y)
	}
	mustPanic(0, 1, 0, "runtime error: integer divide by zero")
	mustPanic(5, 1, 0, "runtime error: integer divide by zero")
	mustPanic(5, 1, 5, "runtime error: integer overflow")
	mustPanic(6, 1, 5, "runtime error: integer overflow")
	mustPanic(^uint64(0), 0, ^uint64(0), "runtime error: integer overflow")
	// no panic just below the boundary
	bits.Div64(4, ^uint64(0), 5)
	bits.Div64(^uint64(0)-1, ^uint64(0), ^uint64(0))
}

// BITS-ADD-64-NOPRE (negative control): with carry = 2 the carry formula is
// out of contract ("The carry input must be 0 or 1; otherwise the behavior is
// undefined"). The Lean counterexample x = y = MaxUint64, carry = 2 is
// reproduced here against the pure-Go formula AND against bits.Add64 as
// compiled (which may be an intrinsic), documenting golang/go#54255 rather
// than claiming a bug.
func TestAdd64CarryTwoIsOutOfContract(t *testing.T) {
	x, y := ^uint64(0), ^uint64(0)
	pureGo := func(x, y, carry uint64) (sum, carryOut uint64) {
		sum = x + y + carry
		carryOut = ((x & y) | ((x | y) &^ sum)) >> 63
		return
	}
	ps, pc := pureGo(x, y, 2)
	// true 128-bit sum is 2^65, i.e. (carryOut, sum) would have to be (2, 0)
	if ps != 0 || pc != 1 {
		t.Fatalf("pure-Go formula gave (%#x,%#x); the Lean model predicts (0,1)", ps, pc)
	}
	s, c := bits.Add64(x, y, 2)
	t.Logf("bits.Add64(MaxUint64, MaxUint64, 2) = (%#x, %#x) on this toolchain (pure-Go formula: (%#x, %#x)); out of contract, not a bug", s, c, ps, pc)
}
