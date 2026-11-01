// Copy of go/tests/bits_test.go:TestAdd64CarryTwoIsOutOfContract (kept here for the record;
// the live test is the one under go/tests).
package tests

import (
	"math/bits"
	"testing"
)

func TestAdd64CarryTwoIsOutOfContract(t *testing.T) {
	x, y := ^uint64(0), ^uint64(0)
	pureGo := func(x, y, carry uint64) (sum, carryOut uint64) {
		sum = x + y + carry
		carryOut = ((x & y) | ((x | y) &^ sum)) >> 63
		return
	}
	ps, pc := pureGo(x, y, 2)
	if ps != 0 || pc != 1 {
		t.Fatalf("pure-Go formula gave (%#x,%#x); the Lean model predicts (0,1)", ps, pc)
	}
	s, c := bits.Add64(x, y, 2)
	t.Logf("bits.Add64(MaxUint64, MaxUint64, 2) = (%#x, %#x); pure-Go formula (%#x, %#x); out of contract", s, c, ps, pc)
}
