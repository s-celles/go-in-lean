//go:build reproduce_findings

// Reproducer for findings/PPC64-POWER10-BSWAP16-MISCOMPILE (GOARCH=ppc64le/ppc64,
// GOPPC64=power10, go1.27 and master). A wrong-code miscompilation (not a memory-safety bug;
// see the canary subtest). Asserts the Go specification, so it FAILS on affected toolchains.
//   GOPPC64=power10 GOOS=linux GOARCH=ppc64le go test -c -tags reproduce_findings -o r.test ./reproducers
//   qemu-ppc64le -cpu power10 ./r.test -test.run Power10Bswap16 -test.v
package reproducers

import (
	"math/bits"
	"testing"
)

//go:noinline
func p10wrong(k uint16, y, z int16) int16 {
	r := ^int16(bits.ReverseBytes16(k))
	if y <= z {
		r = 7
	}
	return r
}

// Canary: if an out-of-bounds read occurred, it would return the sentinel; it does not
// (prove deletes the branch instead), so this must NOT panic and must return 0.
//
//go:noinline
func p10oob(k uint16, s []int8, i int) int8 {
	r := ^int16(bits.ReverseBytes16(k))
	if r < 0 {
		return s[i]
	}
	return 0
}

func TestPower10Bswap16Miscompile(t *testing.T) {
	// 5<=1 is false, so r stays ^ReverseBytes16(0x0400) == ^0x0004 == -5.
	if got := p10wrong(0x0400, 5, 1); got != -5 {
		t.Errorf("p10wrong = %d, spec requires -5 (prove folded the comparison wrongly)", got)
	}
}

func TestPower10Bswap16NoOOB(t *testing.T) {
	// Documents that the miscompilation does NOT cause an out-of-bounds read: prove deletes the
	// s[i] branch, so this returns 0 without reading s[i]. (If it ever returns the sentinel or
	// a non-zero value here, re-open as a memory-safety issue.)
	back := make([]int8, 16)
	for i := range back {
		back[i] = 0x11
	}
	back[8] = 0x7B
	s := back[:4]
	got := p10oob(0x0400, s, 8) // i=8 is out of bounds for len-4 s
	if got != 0 {
		t.Errorf("p10oob returned %#x; a non-zero/sentinel value would mean a real OOB read", got)
	}
}
