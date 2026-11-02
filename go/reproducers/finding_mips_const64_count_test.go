//go:build reproduce_findings

// Reproducer for findings/MIPS-CONST64-COUNT-UINT32 (GOARCH=mips and mipsle, go1.21 .. master).
// Asserts the Go specification, so it FAILS on affected toolchains and passes elsewhere.
//   GOOS=linux GOARCH=mipsle go test -c -tags reproduce_findings -o r.test ./reproducers
//   qemu-mipsel ./r.test -test.run MIPSConst64Count -test.v
package reproducers

import "testing"

//go:noinline
func mcShr(x, y int8) int8 { return (x >> 7) >> (uint64(y) | 0xFFFFFFFF) }

//go:noinline
func mcShl(x uint16, y uint8) uint16 { return (x << 3) << (uint64(y) | 0xFFFFFFFF) }

func TestMIPSConst64Count(t *testing.T) {
	// 127 >> 7 == 0; 0 >> anything == 0. The merged count 7 + 0xFFFFFFFF is lowered as 6.
	if got := mcShr(127, -128); got != 0 {
		t.Errorf("(127 >> 7) >> 0xFFFF_FFFF_FFFF_FFFF = %d, spec requires 0", got)
	}
	// a left shift by >= 16 of a uint16 is 0
	if got := mcShl(1, 0); got != 0 {
		t.Errorf("(1 << 3) << 0xFFFFFFFF = %d, spec requires 0", got)
	}
}
