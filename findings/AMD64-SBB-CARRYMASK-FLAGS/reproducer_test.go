package finding

import "testing"

// golang bug candidate AMD64-SBB-CARRYMASK-FLAGS (see finding.md).
// Wrong code on linux/amd64, go1.24.13 .. go1.27.3 and master 2b74366d:
// the y == 64 SETcc reads the flags clobbered by the shift mask's SBBQ.

//go:noinline
func lshEq(x, y uint64) uint64 {
	r := x << y
	eq := uint64(0)
	if y == 64 {
		eq = 1
	}
	return r + eq
}

//go:noinline
func rshS(x int64, y uint64) int64 {
	r := x >> y
	eq := int64(0)
	if y == 64 {
		eq = 1
	}
	return r + eq
}

//go:noinline
func lsh32(x uint32, y uint64) uint32 {
	r := x << y
	eq := uint32(0)
	if y == 32 {
		eq = 1
	}
	return r + eq
}

// 386 form (go1.24.13 .. go1.27.3): the decomposed comparison shares
// CMPLconst [1] hi with the shift count saturation; SETEQ reads post-SBBL flags.
//
//go:noinline
func cmpSat(x int16) int16 {
	r := int16(-2047) << uint64(uint64(x))
	if uint64(x) <= 8589934591 { // false for negative x
		r = int16(x) &^ 3
	}
	return r
}

func TestSBBcarrymaskFlags(t *testing.T) {
	if got := lshEq(1, 65); got != 0 {
		t.Errorf("lshEq(1, 65) = %d, want 0", got)
	}
	if got := lshEq(1, 63); got != 9223372036854775808 {
		t.Errorf("lshEq(1, 63) = %d, want 9223372036854775808", got)
	}
	if got := lshEq(1, 64); got != 1 {
		t.Errorf("lshEq(1, 64) = %d, want 1", got)
	}
	if got := rshS(-1, 65); got != -1 {
		t.Errorf("rshS(-1, 65) = %d, want -1", got)
	}
	if got := lsh32(1, 33); got != 0 {
		t.Errorf("lsh32(1, 33) = %d, want 0", got)
	}
	if got := cmpSat(-1); got != 0 {
		t.Errorf("cmpSat(-1) = %d, want 0", got)
	}
	if got := cmpSat(5); got != 4 { // 5 <= 0x1FFFFFFFF: branch taken, 5 &^ 3 = 4
		t.Errorf("cmpSat(5) = %d, want 4", got)
	}
}
