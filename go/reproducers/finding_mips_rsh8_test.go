//go:build reproduce_findings

// Reproducer for findings/MIPS-RSH8-SIGNEXT16 (GOARCH=mips and mipsle, go1.8 .. master).
// Asserts the Go specification, so it FAILS on affected toolchains and passes elsewhere.
// Run (under qemu user-mode emulation):
//   GOOS=linux GOARCH=mipsle go test -c -tags reproduce_findings -o r.test ./reproducers
//   qemu-mipsel ./r.test -test.run MIPSRsh8 -test.v
package reproducers

import "testing"

// A signed 8-bit right shift by a variable count, applied to a value that is still a raw
// 32-bit ALU result (MUL, ADDU): MIPS.rules sign-extends it from bit 15 instead of bit 7.

//go:noinline
func mulShr8(x, k int8, s uint64) int8 { return (x * k) >> s }

//go:noinline
func addShr8(x, k int8, s uint32) int8 { return (x + k) >> s }

//go:noinline
func mulShr8by8(x, k int8, s uint8) int8 { return (x * k) >> s }

func TestMIPSRsh8SignExt(t *testing.T) {
	// 127 * -15 = -1905; as int8 that is -113 (0x8F). -113 >> 8 == -1.
	if got := mulShr8(127, -15, 8); got != -1 {
		t.Errorf("int8(127 * -15) >> 8 = %d, spec requires -1", got)
	}
	// 127 + 1 wraps to -128; -128 >> 8 == -1.
	if got := addShr8(127, 1, 8); got != -1 {
		t.Errorf("int8(127 + 1) >> 8 = %d, spec requires -1", got)
	}
	// -113 >> 3 == -15 (count below 8 is affected too: bits 8-15 shift into the result).
	if got := mulShr8by8(127, -15, 3); got != -15 {
		t.Errorf("int8(127 * -15) >> 3 = %d, spec requires -15", got)
	}
}
