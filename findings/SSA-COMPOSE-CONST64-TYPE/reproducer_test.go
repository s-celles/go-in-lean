//go:build reproduce_findings

// Reproducer for findings/SSA-COMPOSE-CONST64-TYPE (Go master babb75be; go1.27.3 is correct).
// Asserts the Go specification, so it FAILS on affected toolchains.
// Run: go test -tags reproduce_findings ./reproducers -run ComposeConst64 -v
package reproducers

import "testing"

// Inlinable helpers: the constant counts reach the shifts through inlining (go vet stays quiet).
func shr2x32(y int32, a, b uint64) int32 { return (y >> a) >> b }
func shr2x16(y int16, a, b uint64) int16 { return (y >> a) >> b }

//go:noinline
func ccInt32(y int32) int32 { return shr2x32(y, 1, 1<<62) }

//go:noinline
func ccInt16(y int16) int16 { return shr2x16(y, 1, 1<<32) }

func TestComposeConst64Type(t *testing.T) {
	// spec: shifting right by >= width gives 0 for non-negative and -1 for negative values
	if got := ccInt32(2); got != 0 {
		t.Errorf("(int32(2) >> 1) >> (1<<62) = %d, spec requires 0", got)
	}
	if got := ccInt32(-5); got != -1 {
		t.Errorf("(int32(-5) >> 1) >> (1<<62) = %d, spec requires -1", got)
	}
	if got := ccInt16(3); got != 0 {
		t.Errorf("(int16(3) >> 1) >> (1<<32) = %d, spec requires 0", got)
	}
}
