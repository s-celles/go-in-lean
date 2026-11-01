// Command vectors_slices enumerates the same configurations as
// `lake exe slicesearch N` and records what the real slices.Insert,
// slices.Delete and slices.Replace of the pinned toolchain return,
// including the state of the backing array afterwards. The Lean checker
// (`lake exe checkslices`) re-runs the model on each configuration and
// fails on any difference. Output: JSON lines.
//
// Backing array a has values 1..N; a second array b has 101..N+100 (for the
// non-aliasing case). s = a[off:off+len:off+cap]; v = a[x:x+l] or b[x:x+l].
package main

import (
	"encoding/json"
	"fmt"
	"os"
	"slices"
	"strconv"
)

type Rec struct {
	Fn     string `json:"fn"`
	N      int    `json:"n"`
	S      [3]int `json:"s"`
	VAlias bool   `json:"v_alias"`
	V      [2]int `json:"v"`
	I      int    `json:"i"`
	J      int    `json:"j"`
	Result []int  `json:"result"`
	Arr    []int  `json:"arr"` // backing array a after the call
	Panic  string `json:"panic,omitempty"`
}

func fresh(n int) ([]int, []int) {
	a := make([]int, n)
	b := make([]int, n)
	for k := range a {
		a[k] = k + 1
		b[k] = k + 101
	}
	return a, b
}

func catch(f func()) (p string) {
	defer func() {
		if e := recover(); e != nil {
			p = fmt.Sprint(e)
		}
	}()
	f()
	return ""
}

func main() {
	n := 5
	if len(os.Args) > 1 {
		n, _ = strconv.Atoi(os.Args[1])
	}
	enc := json.NewEncoder(os.Stdout)
	emit := func(r Rec) {
		if err := enc.Encode(r); err != nil {
			panic(err)
		}
	}
	for soff := 0; soff <= n; soff++ {
		for scap := 0; scap <= n-soff; scap++ {
			for slen := 0; slen <= scap; slen++ {
				for _, valias := range []bool{true, false} {
					for voff := 0; voff <= n; voff++ {
						for vlen := 0; vlen <= n-voff; vlen++ {
							for i := 0; i <= slen; i++ {
								{ // Insert
									a, b := fresh(n)
									s := a[soff : soff+slen : soff+scap]
									v := b[voff : voff+vlen]
									if valias {
										v = a[voff : voff+vlen]
									}
									var r []int
									p := catch(func() { r = slices.Insert(s, i, v...) })
									emit(Rec{"Insert", n, [3]int{soff, slen, scap}, valias, [2]int{voff, vlen}, i, i, slices.Clone(r), a, p})
								}
								for j := i; j <= slen; j++ {
									a, b := fresh(n)
									s := a[soff : soff+slen : soff+scap]
									v := b[voff : voff+vlen]
									if valias {
										v = a[voff : voff+vlen]
									}
									var r []int
									p := catch(func() { r = slices.Replace(s, i, j, v...) })
									emit(Rec{"Replace", n, [3]int{soff, slen, scap}, valias, [2]int{voff, vlen}, i, j, slices.Clone(r), a, p})
									if valias && voff == 0 && vlen == 0 {
										a, _ := fresh(n)
										s := a[soff : soff+slen : soff+scap]
										var r []int
										p := catch(func() { r = slices.Delete(s, i, j) })
										emit(Rec{"Delete", n, [3]int{soff, slen, scap}, true, [2]int{0, 0}, i, j, slices.Clone(r), a, p})
									}
								}
							}
						}
					}
				}
			}
		}
	}
}
