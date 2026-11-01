// Boundary tests for the length-overflow guards of strings/bytes/slices
// (GoInLean/Stdlib/Overflow.lean). Huge lengths are obtained with
// unsafe.String / unsafe.Slice over a 1-byte buffer: the guards run before
// any element is read, so no memory beyond that byte is touched. Only cases
// that end in a recoverable panic or a small result are exercised; a case
// that passes the guard with a huge length would attempt a fatal allocation.
package tests

import (
	"bytes"
	"math"
	"slices"
	"strings"
	"testing"
	"unsafe"
)

var one = []byte{'a'}

func huge(n int) string      { return unsafe.String(&one[0], n) }
func hugeSlice(n int) []byte { return unsafe.Slice(&one[0], n) }

func panicMsg(f func()) (msg string) {
	defer func() {
		if e := recover(); e != nil {
			msg = strings.TrimSpace(strings.Split(func() string {
				if err, ok := e.(error); ok {
					return err.Error()
				}
				return e.(string)
			}(), "\n")[0])
		}
	}()
	f()
	return ""
}

// REPEAT-GUARD-EXACT: panics exactly when len*count > MaxInt.
func TestRepeatGuardBoundary(t *testing.T) {
	half := math.MaxInt/2 + 1 // 2*half = MaxInt+1: overflow
	if m := panicMsg(func() { strings.Repeat(huge(half), 2) }); m != "strings: Repeat output length overflow" {
		t.Errorf("strings.Repeat(len=%d, 2): panic %q", half, m)
	}
	if m := panicMsg(func() { _ = slices.Repeat(hugeSlice(half), 2) }); m != "the result of (len(x) * count) overflows" {
		t.Errorf("slices.Repeat(len=%d, 2): panic %q", half, m)
	}
	// 3-way split, product overflows by one
	third := math.MaxInt/3 + 1
	if m := panicMsg(func() { strings.Repeat(huge(third), 3) }); m != "strings: Repeat output length overflow" {
		t.Errorf("strings.Repeat(len=%d, 3): panic %q", third, m)
	}
	// small cases: exact result
	if strings.Repeat("ab", 3) != "ababab" || strings.Repeat("", math.MaxInt) != "" {
		t.Error("small Repeat wrong")
	}
}

// CONCAT-GUARD-EXACT: panics "len out of range" exactly when the total exceeds MaxInt.
func TestConcatGuardBoundary(t *testing.T) {
	a := hugeSlice(math.MaxInt / 2)
	b := hugeSlice(math.MaxInt/2 + 2) // total MaxInt+1
	if m := panicMsg(func() { _ = slices.Concat(a, b) }); m != "len out of range" {
		t.Errorf("slices.Concat total MaxInt+1: panic %q", m)
	}
}

// JOIN-GUARD-CONSERVATIVE: with 4 elements (k = 3 separators) and len(sep) = MaxInt/3,
// the exact output length is 3*(MaxInt/3) = MaxInt-1, which fits in an int, yet Join
// reports an overflow. Documented as a conservative (sound, not exact) guard; see
// findings/JOIN-GUARD-CONSERVATIVE. The alternative would be an unrecoverable
// out-of-memory error, so this is not a defect.
func TestJoinGuardConservative(t *testing.T) {
	sep := huge(math.MaxInt / 3)
	exact := uint64(len(sep)) * 3
	if exact > math.MaxInt {
		t.Fatalf("precondition: exact length %d should fit in int", exact)
	}
	if m := panicMsg(func() { strings.Join([]string{"", "", "", ""}, sep) }); m != "strings: Join output length overflow" {
		t.Errorf("strings.Join: panic %q", m)
	}
	if m := panicMsg(func() { bytes.Join([][]byte{{}, {}, {}, {}}, hugeSlice(math.MaxInt/3)) }); m != "bytes: Join output length overflow" {
		t.Errorf("bytes.Join: panic %q", m)
	}
}
