package main

import "fmt"

// With -gcflags=-N (the flags debuggers use), uint32(x) ^ uint32(x) is not folded
// before lowering, so the AMD64 rules see MOVLQZX (ANDL t (NOTL (XORL t t))).
// (MOVLQZX (ANDLconst [c] x)) => (ANDLconst [c] x) drops the zero extension, then
// (ANDLconst [-1] x) => x drops the ANDL, and the full 64-bit register of x is
// returned: golang/go#36897.
//
//go:noinline
func f(x uint64) uint64 { return uint64(uint32(x) &^ (uint32(x) ^ uint32(x))) }

func main() { fmt.Println(f(1<<63 | 5)) } // want 5
