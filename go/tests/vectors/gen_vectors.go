// Command gen_vectors prints a JSON table of inputs and outputs of the
// math/bits functions as computed by the *pinned Go toolchain*. The table
// is consumed by `scripts/check_vectors.lean`, which evaluates the Lean
// models on the same inputs and fails on any disagreement. This is the
// model-validation step (differential testing) that must pass before any
// theorem about the model is allowed to say anything about Go.
//
// Inputs are deterministic: boundary values, single bits, and a fixed-seed
// PRNG. Run: go run ./tests/vectors > ../targets/vectors/bits.json
package main

import (
	"encoding/json"
	"fmt"
	"math/bits"
	"math/rand/v2"
	"os"
)

type Vec struct {
	Fn  string   `json:"fn"`
	In  []uint64 `json:"in"`
	Out []uint64 `json:"out"`
	// Panic is set to the panic message's category when the call panics.
	Panic string `json:"panic,omitempty"`
}

func inputs64(r *rand.Rand) []uint64 {
	xs := []uint64{0, 1, 2, 3, 0x7f, 0x80, 0xff, 0x100, 0x7fff, 0x8000, 0xffff, 0x10000,
		0x7fffffff, 0x80000000, 0xffffffff, 0x100000000, 0x7fffffffffffffff, 0x8000000000000000,
		0xffffffffffffffff, 0xfffffffffffffffe, 0x5555555555555555, 0xaaaaaaaaaaaaaaaa,
		0x0123456789abcdef, 0xfedcba9876543210}
	for i := 0; i < 64; i++ {
		xs = append(xs, uint64(1)<<i, ^(uint64(1) << i))
	}
	for i := 0; i < 100; i++ {
		xs = append(xs, r.Uint64())
	}
	return xs
}

func catch(f func()) (p string) {
	defer func() {
		if e := recover(); e != nil {
			switch fmt.Sprint(e) {
			case "runtime error: integer divide by zero":
				p = "divideError"
			case "runtime error: integer overflow":
				p = "overflowError"
			default:
				p = "other: " + fmt.Sprint(e)
			}
		}
	}()
	f()
	return ""
}

func main() {
	r := rand.New(rand.NewPCG(20261101, 42))
	xs := inputs64(r)
	var vs []Vec
	u := func(b bool) uint64 {
		if b {
			return 1
		}
		return 0
	}
	_ = u
	for _, x := range xs {
		x8, x16, x32 := uint8(x), uint16(x), uint32(x)
		vs = append(vs,
			Vec{"Len8", []uint64{uint64(x8)}, []uint64{uint64(bits.Len8(x8))}, ""},
			Vec{"Len16", []uint64{uint64(x16)}, []uint64{uint64(bits.Len16(x16))}, ""},
			Vec{"Len32", []uint64{uint64(x32)}, []uint64{uint64(bits.Len32(x32))}, ""},
			Vec{"Len64", []uint64{x}, []uint64{uint64(bits.Len64(x))}, ""},
			Vec{"LeadingZeros64", []uint64{x}, []uint64{uint64(bits.LeadingZeros64(x))}, ""},
			Vec{"TrailingZeros8", []uint64{uint64(x8)}, []uint64{uint64(bits.TrailingZeros8(x8))}, ""},
			Vec{"TrailingZeros16", []uint64{uint64(x16)}, []uint64{uint64(bits.TrailingZeros16(x16))}, ""},
			Vec{"TrailingZeros32", []uint64{uint64(x32)}, []uint64{uint64(bits.TrailingZeros32(x32))}, ""},
			Vec{"TrailingZeros64", []uint64{x}, []uint64{uint64(bits.TrailingZeros64(x))}, ""},
			Vec{"OnesCount8", []uint64{uint64(x8)}, []uint64{uint64(bits.OnesCount8(x8))}, ""},
			Vec{"OnesCount16", []uint64{uint64(x16)}, []uint64{uint64(bits.OnesCount16(x16))}, ""},
			Vec{"OnesCount32", []uint64{uint64(x32)}, []uint64{uint64(bits.OnesCount32(x32))}, ""},
			Vec{"OnesCount64", []uint64{x}, []uint64{uint64(bits.OnesCount64(x))}, ""},
			Vec{"Reverse8", []uint64{uint64(x8)}, []uint64{uint64(bits.Reverse8(x8))}, ""},
			Vec{"Reverse16", []uint64{uint64(x16)}, []uint64{uint64(bits.Reverse16(x16))}, ""},
			Vec{"Reverse32", []uint64{uint64(x32)}, []uint64{uint64(bits.Reverse32(x32))}, ""},
			Vec{"Reverse64", []uint64{x}, []uint64{bits.Reverse64(x)}, ""},
			Vec{"ReverseBytes16", []uint64{uint64(x16)}, []uint64{uint64(bits.ReverseBytes16(x16))}, ""},
			Vec{"ReverseBytes32", []uint64{uint64(x32)}, []uint64{uint64(bits.ReverseBytes32(x32))}, ""},
			Vec{"ReverseBytes64", []uint64{x}, []uint64{bits.ReverseBytes64(x)}, ""},
		)
		for _, k := range []int{0, 1, 7, 8, 9, 31, 32, 33, 63, 64, 65, -1, -7, -8, -63, -64, -65, 1 << 40, -(1 << 40), int(x)} {
			ku := uint64(k)
			vs = append(vs,
				Vec{"RotateLeft8", []uint64{uint64(x8), ku}, []uint64{uint64(bits.RotateLeft8(x8, k))}, ""},
				Vec{"RotateLeft16", []uint64{uint64(x16), ku}, []uint64{uint64(bits.RotateLeft16(x16, k))}, ""},
				Vec{"RotateLeft32", []uint64{uint64(x32), ku}, []uint64{uint64(bits.RotateLeft32(x32, k))}, ""},
				Vec{"RotateLeft64", []uint64{x, ku}, []uint64{bits.RotateLeft64(x, k)}, ""},
			)
		}
	}
	// binary / ternary functions on a subsample of pairs
	for i := 0; i < len(xs); i += 5 {
		for j := 1; j < len(xs); j += 13 {
			x, y := xs[i], xs[j]
			for _, c := range []uint64{0, 1} {
				s, co := bits.Add64(x, y, c)
				vs = append(vs, Vec{"Add64", []uint64{x, y, c}, []uint64{s, co}, ""})
				d, bo := bits.Sub64(x, y, c)
				vs = append(vs, Vec{"Sub64", []uint64{x, y, c}, []uint64{d, bo}, ""})
				s32, co32 := bits.Add32(uint32(x), uint32(y), uint32(c))
				vs = append(vs, Vec{"Add32", []uint64{uint64(uint32(x)), uint64(uint32(y)), c}, []uint64{uint64(s32), uint64(co32)}, ""})
				d32, bo32 := bits.Sub32(uint32(x), uint32(y), uint32(c))
				vs = append(vs, Vec{"Sub32", []uint64{uint64(uint32(x)), uint64(uint32(y)), c}, []uint64{uint64(d32), uint64(bo32)}, ""})
			}
			hi, lo := bits.Mul64(x, y)
			vs = append(vs, Vec{"Mul64", []uint64{x, y}, []uint64{hi, lo}, ""})
			hi32, lo32 := bits.Mul32(uint32(x), uint32(y))
			vs = append(vs, Vec{"Mul32", []uint64{uint64(uint32(x)), uint64(uint32(y))}, []uint64{uint64(hi32), uint64(lo32)}, ""})
			// Div64(hi, lo, y): use x as y (divisor), y as lo, and a reduced hi
			for _, hiv := range []uint64{0, x >> 1, x - 1, x} {
				var q, rm uint64
				p := catch(func() { q, rm = bits.Div64(hiv, y, x) })
				if p == "" {
					vs = append(vs, Vec{"Div64", []uint64{hiv, y, x}, []uint64{q, rm}, ""})
				} else {
					vs = append(vs, Vec{"Div64", []uint64{hiv, y, x}, nil, p})
				}
				var rem uint64
				p = catch(func() { rem = bits.Rem64(hiv, y, x) })
				if p == "" {
					vs = append(vs, Vec{"Rem64", []uint64{hiv, y, x}, []uint64{rem}, ""})
				} else {
					vs = append(vs, Vec{"Rem64", []uint64{hiv, y, x}, nil, p})
				}
				var q32, r32 uint32
				p = catch(func() { q32, r32 = bits.Div32(uint32(hiv), uint32(y), uint32(x)) })
				if p == "" {
					vs = append(vs, Vec{"Div32", []uint64{uint64(uint32(hiv)), uint64(uint32(y)), uint64(uint32(x))}, []uint64{uint64(q32), uint64(r32)}, ""})
				} else {
					vs = append(vs, Vec{"Div32", []uint64{uint64(uint32(hiv)), uint64(uint32(y)), uint64(uint32(x))}, nil, p})
				}
			}
		}
	}
	enc := json.NewEncoder(os.Stdout)
	if err := enc.Encode(vs); err != nil {
		panic(err)
	}
}
