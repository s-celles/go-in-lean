//go:build reproduce_findings

// Reproducer for findings/PROVE-EXT-CONST-TRUNC (all GOARCH; go1.26.6 .. go1.26.10, go1.27.3 and
// master; simpler shapes from go1.24). Asserts the Go specification, so it FAILS on affected
// toolchains and passes elsewhere.
//   go test -tags reproduce_findings ./reproducers -run ProveExtConst -v
package reproducers

import "testing"

var proveSink int

// int16(x)-513 is in [-513, -258], so the comparison is always false.
//
//go:noinline
func proveExtConst(x uint8) {
	if int32(int16(x)-513) < -536870911 {
		proveSink = 1
	}
}

func TestProveExtConst(t *testing.T) {
	for _, x := range []uint8{0, 1, 128, 255} {
		proveSink = 0
		proveExtConst(x)
		if proveSink != 0 {
			t.Errorf("x=%d: branch taken although int32(int16(x)-513) >= -513 > -536870911", x)
		}
	}
}
