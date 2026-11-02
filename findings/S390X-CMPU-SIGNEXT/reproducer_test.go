//go:build reproduce_findings

// Reproducer for findings/S390X-CMPU-SIGNEXT (GOARCH=s390x, go1.26 .. master).
// Asserts the Go specification, so it FAILS on affected toolchains and passes elsewhere.
//   GOOS=linux GOARCH=s390x go test -c -tags reproduce_findings -o r.test ./reproducers
//   qemu-s390x ./r.test -test.run S390XCmpu -test.v
package reproducers

import "testing"

//go:noinline
func szLessB(y int8) bool { return uint64(y) < 0xFFFFFFFF }

//go:noinline
func szLeqH(y int16) bool { return uint64(y) <= 0xFFFFFFF0 }

//go:noinline
func szEqB(y int8) bool { return uint64(y) == 0xFFFFFF80 }

func TestS390XCmpuSignExt(t *testing.T) {
	// uint64(int8(-128)) == 0xFFFFFFFFFFFFFF80, which is not below 0xFFFFFFFF.
	if szLessB(-128) {
		t.Errorf("uint64(int8(-128)) < 0xFFFFFFFF = true, spec requires false")
	}
	// uint64(int16(-20)) == 0xFFFFFFFFFFFFFFEC, which is not <= 0xFFFFFFF0.
	if szLeqH(-20) {
		t.Errorf("uint64(int16(-20)) <= 0xFFFFFFF0 = true, spec requires false")
	}
	// uint64(int8(-128)) != 0xFFFFFF80 (it differs in the upper 32 bits).
	if szEqB(-128) {
		t.Errorf("uint64(int8(-128)) == 0xFFFFFF80 = true, spec requires false")
	}
	if !szLessB(5) || !szLeqH(5) {
		t.Errorf("small values: spec requires true")
	}
}
