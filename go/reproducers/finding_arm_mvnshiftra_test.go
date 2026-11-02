//go:build reproduce_findings

// Reproducer for findings/ARM-MVNSHIFTRA-CONST (GOARCH=arm, go1.16 .. master).
// Asserts the Go specification, so it FAILS on affected toolchains and passes elsewhere.
//   GOOS=linux GOARCH=arm go test -c -tags reproduce_findings -o r.test ./reproducers
//   qemu-arm ./r.test -test.run ARMMvnShiftRA -test.v
package reproducers

import (
	"math/bits"
	"testing"
)

// The low word of the argument folds to the constant 0 only during lowering (OnesCount16 of a
// constant is a table load on arm), so Ctz64's 32-bit decomposition meets MVNshiftRA of a constant.
//
//go:noinline
func armCtz64Zero() int {
	return bits.TrailingZeros64(uint64(uint16(bits.OnesCount16(16384))) &^ 16777217)
}

func TestARMMvnShiftRA(t *testing.T) {
	if got := armCtz64Zero(); got != 64 {
		t.Errorf("TrailingZeros64(0) = %d, spec requires 64", got)
	}
}
