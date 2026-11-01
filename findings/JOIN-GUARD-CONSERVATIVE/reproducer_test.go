// See go/tests/overflow_test.go (TestJoinGuardConservative) for the live test.
package tests

import (
	"math"
	"strings"
	"testing"
	"unsafe"
)

func TestJoinGuardConservativeStandalone(t *testing.T) {
	one := []byte{'a'}
	sep := unsafe.String(&one[0], math.MaxInt/3) // exact output length 3*len(sep) = MaxInt-1
	defer func() {
		if r := recover(); r != "strings: Join output length overflow" {
			t.Fatalf("got %v", r)
		}
	}()
	_ = strings.Join([]string{"", "", "", ""}, sep)
}
