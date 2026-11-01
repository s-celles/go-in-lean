// Property tests mirroring GoInLean/Properties/Slices.lean on the real
// standard library (slices, sort).
package tests

import (
	"math"
	"math/rand/v2"
	"slices"
	"sort"
	"testing"
)

// SORT-SEARCH-MID: int(uint(i+j)>>1) == floor((i+j)/2) with i <= h < j, incl. near MaxInt.
func TestSearchMidpoint(t *testing.T) {
	cases := [][2]int{{0, 0}, {0, 1}, {1, 1}, {0, math.MaxInt}, {1, math.MaxInt}, {math.MaxInt - 1, math.MaxInt},
		{math.MaxInt / 2, math.MaxInt}, {math.MaxInt, math.MaxInt}, {3, 8}}
	for _, c := range cases {
		i, j := c[0], c[1]
		h := int(uint(i+j) >> 1)
		// oracle: exact floor((i+j)/2) via uint64 arithmetic without overflow (i, j >= 0)
		var want int
		if (i%2 == 1) && (j%2 == 1) {
			want = i/2 + j/2 + 1
		} else {
			want = i/2 + j/2
		}
		if h != want {
			t.Errorf("midpoint(%d,%d) = %d, want %d", i, j, h, want)
		}
		if i < j && !(i <= h && h < j) {
			t.Errorf("midpoint(%d,%d) = %d violates i <= h < j", i, j, h)
		}
		// SORT-SEARCH-MID-NAIVE: show the naive version really overflows for i = 1, j = MaxInt
		if i == 1 && j == math.MaxInt && (i+j)/2 >= 0 {
			t.Errorf("expected the naive (i+j)/2 to overflow negative, got %d", (i+j)/2)
		}
	}
}

// SORT-SEARCH-SPEC: smallest index with f true for monotone f, else n (oracle: linear scan).
func TestSearchSpec(t *testing.T) {
	r := rand.New(rand.NewPCG(1, 2))
	for iter := 0; iter < 2000; iter++ {
		n := r.IntN(40)
		thr := r.IntN(n + 2) // threshold may be n+1 (f never true)
		f := func(i int) bool { return i >= thr }
		got := sort.Search(n, f)
		want := n
		for k := 0; k < n; k++ {
			if f(k) {
				want = k
				break
			}
		}
		if got != want {
			t.Fatalf("Search(%d, >=%d) = %d, want %d", n, thr, got, want)
		}
	}
}

// SLICES-COMPACT-NOADJ: no adjacent duplicates, sublist, head preserved, length <=.
func TestCompactSpec(t *testing.T) {
	r := rand.New(rand.NewPCG(3, 4))
	isSublist := func(sub, s []int) bool {
		i := 0
		for _, x := range s {
			if i < len(sub) && sub[i] == x {
				i++
			}
		}
		return i == len(sub)
	}
	for iter := 0; iter < 2000; iter++ {
		n := r.IntN(12)
		s := make([]int, n)
		for i := range s {
			s[i] = r.IntN(3)
		}
		orig := slices.Clone(s)
		c := slices.Compact(s)
		for k := 1; k < len(c); k++ {
			if c[k] == c[k-1] {
				t.Fatalf("Compact(%v) = %v has adjacent duplicates", orig, c)
			}
		}
		if !isSublist(c, orig) {
			t.Fatalf("Compact(%v) = %v is not a sublist", orig, c)
		}
		if len(orig) > 0 && (len(c) == 0 || c[0] != orig[0]) {
			t.Fatalf("Compact(%v) = %v lost the head", orig, c)
		}
		if len(c) > len(orig) {
			t.Fatalf("Compact grew: %v -> %v", orig, c)
		}
	}
}

// SLICES-INDEX-CONTAINS
func TestIndexContainsSpec(t *testing.T) {
	r := rand.New(rand.NewPCG(5, 6))
	for iter := 0; iter < 2000; iter++ {
		n := r.IntN(10)
		s := make([]int, n)
		for i := range s {
			s[i] = r.IntN(5)
		}
		v := r.IntN(6)
		idx := slices.Index(s, v)
		in := slices.Contains(s, v)
		if (idx == -1) != !in {
			t.Fatalf("Index(%v,%d)=%d but Contains=%v", s, v, idx, in)
		}
		if idx >= 0 {
			if s[idx] != v {
				t.Fatalf("Index(%v,%d)=%d but s[idx]=%d", s, v, idx, s[idx])
			}
			for k := 0; k < idx; k++ {
				if s[k] == v {
					t.Fatalf("Index(%v,%d)=%d but earlier match at %d", s, v, idx, k)
				}
			}
		} else {
			for _, x := range s {
				if x == v {
					t.Fatalf("Index(%v,%d)=-1 but v present", s, v)
				}
			}
		}
	}
}
