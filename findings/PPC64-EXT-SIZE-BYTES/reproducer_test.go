//go:build reproduce_findings

// Reproducer for findings/PPC64-EXT-SIZE-BYTES (GOARCH=ppc64 and ppc64le, go1.21 .. master).
// Asserts the Go specification, so it FAILS on affected toolchains and passes elsewhere.
//   GOOS=linux GOARCH=ppc64le go test -c -tags reproduce_findings -o r.test ./reproducers
//   qemu-ppc64le ./r.test -test.run PPC64Ext -test.v
package reproducers

import "testing"

//go:noinline
func ppcTrunc16(x int32) int32 { return int32(int16(x >> 1)) }

//go:noinline
func ppcTrunc16U(x uint32) uint32 { return uint32(uint16(x >> 1)) }

//go:noinline
func ppcCmp16(x int64) bool { return int16(int32(x)>>8) < -513 }

//go:noinline
func ppcTrunc8(x int64) int64 { return int64(int8(int32(x) >> 1)) }

func TestPPC64ExtSizeBytes(t *testing.T) {
	// int16(-2^31 >> 1) == int16(-2^30) == 0
	if got := ppcTrunc16(-1 << 31); got != 0 {
		t.Errorf("int32(int16(-2^31 >> 1)) = %d, spec requires 0", got)
	}
	if got := ppcTrunc16U(1 << 31); got != 0 {
		t.Errorf("uint32(uint16(2^31 >> 1)) = %d, spec requires 0", got)
	}
	// int16(int32(0x80000000) >> 8) == int16(0xFF800000) == 0, not < -513
	if ppcCmp16(0x80000000) {
		t.Errorf("int16(int32(0x80000000)>>8) < -513 = true, spec requires false")
	}
	if got := ppcTrunc8(0x80000000); got != 0 {
		t.Errorf("int64(int8(int32(0x80000000) >> 1)) = %d, spec requires 0", got)
	}
}
