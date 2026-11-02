//go:build reproduce_findings

// Reproducer for findings/ARM64-CSINV-NOT (GOARCH=arm64, go1.21 .. master; native on Apple
// Silicon and other arm64 hosts). Asserts the Go specification, so it FAILS on affected
// toolchains and passes elsewhere.
//   go test -tags reproduce_findings ./reproducers -run ARM64Csinv -v
package reproducers

import (
	"math/bits"
	"testing"
)

//go:noinline
func csinvSel(x, y int64) int64 {
	r := x >> 33
	if bits.OnesCount8(128) > 0 { // true; known only after lowering (table load)
		r = ^y
	}
	return r
}

func TestARM64CsinvNot(t *testing.T) {
	if got := csinvSel(0, 2); got != -3 {
		t.Errorf("^2 selected by a constant-true condition = %d, spec requires -3", got)
	}
	if got := csinvSel(5, 0); got != -1 {
		t.Errorf("^0 selected by a constant-true condition = %d, spec requires -1", got)
	}
}
