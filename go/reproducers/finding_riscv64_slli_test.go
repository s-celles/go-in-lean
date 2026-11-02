//go:build reproduce_findings

// Reproducer for findings/RISCV64-SLLI-NARROW-TYPE (GOARCH=riscv64, go1.26 .. master).
// Asserts the Go specification, so it FAILS on affected toolchains and passes elsewhere.
//   GOOS=linux GOARCH=riscv64 go test -c -tags reproduce_findings -o r.test ./reproducers
//   qemu-riscv64 ./r.test -test.run RISCV64Slli -test.v
package reproducers

import "testing"

//go:noinline
func rvSubNeg8(x int8) int8 { return (x - (-x)) >> 8 }

//go:noinline
func rvSubNeg16(x int16) int16 { return (x - (-x)) >> 16 }

//go:noinline
func rvSubNegCSE(a int8) int8 { b := -a; return (a - b) >> 9 }

func TestRISCV64SlliNarrowType(t *testing.T) {
	// int8(-1 - 1) == -2; -2 >> 8 == -1 (sign fill). The compiled code returns the constant 0.
	if got := rvSubNeg8(-1); got != -1 {
		t.Errorf("int8(-1 - (-(-1))) >> 8 = %d, spec requires -1", got)
	}
	if got := rvSubNeg16(-3); got != -1 {
		t.Errorf("int16(-3 - 3) >> 16 = %d, spec requires -1", got)
	}
	if got := rvSubNegCSE(-5); got != -1 {
		t.Errorf("b := -a; (a - b) >> 9 with a = -5: %d, spec requires -1", got)
	}
}
