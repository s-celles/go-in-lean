//go:build reproduce_findings

// Reproducer for findings/SSA-SHIFTMASK-SIGNED-COUNT (go1.25.5): the generic SSA rules
// `((x >> c) & d) << e` (generic.rules:522-530) compare the constant shift counts as signed
// int64, so a constant count c >= 2^63 on a signed value is rewritten incorrectly.
// These tests assert the Go SPECIFICATION and therefore FAIL on affected toolchains.
// Run: go test -tags reproduce_findings ./reproducers -run ShiftMask -v
package reproducers

import "testing"

//go:noinline
func smConst(x int64) int64 { return ((x >> uint64(1<<63)) & 3) << 1 }

//go:noinline
func smVar(x int64, n uint64) int64 { return ((x >> n) & 3) << 1 }

func smField(x int64, shift uint64, mask int64) int64 { return (x >> shift) & mask }

//go:noinline
func smInlined(x int64) int64 { return smField(x, ^uint64(0), 3) << 1 }

func TestShiftMaskHugeConstCount(t *testing.T) {
	// spec: -1 >> 2^63 == -1; -1 & 3 == 3; 3 << 1 == 6
	if got := smConst(-1); got != 6 {
		t.Errorf("((-1 >> (1<<63)) & 3) << 1 = %d, spec requires 6 (variable-count version gives %d)", got, smVar(-1, 1<<63))
	}
}

func TestShiftMaskViaInlining(t *testing.T) {
	// spec: 1 >> MaxUint64 == 0, so the result is 0; -1 gives 6
	if got := smInlined(1); got != 0 {
		t.Errorf("inlined field(1, ^uint64(0), 3) << 1 = %d, spec requires 0", got)
	}
	if got := smInlined(-1); got != 6 {
		t.Errorf("inlined field(-1, ^uint64(0), 3) << 1 = %d, spec requires 6", got)
	}
}
