# amd64: `-N` builds drop a zero extension (`ANDLconst [-1]`), golang/go#36897

**Status:** reproduced on go1.26.10, go1.27.3 and tip `56ae71df05` (amd64 only; arm64,
riscv64, ppc64le, s390x and 386 are correct). A concrete trigger for the latent issue
golang/go#36897 (open since 2020, "not sure whether it is possible to trigger this bug
right now").

**Human review status:** reviewed; posted as a [comment on #36897](https://github.com/golang/go/issues/36897#issuecomment-6689152845) on 2026-11-06.

## Reproducer

`reproducer.go`: `uint64(uint32(x) &^ (uint32(x) ^ uint32(x)))` returns `x` instead of
`uint64(uint32(x))` when compiled with `-gcflags=-N` (with or without `-l`):

```
go run -gcflags='-N -l' reproducer.go   # 9223372036854775813, want 5
go run reproducer.go                    # 5
```

## Root cause

With `-N` there is no generic CSE, so the two `Trunc64to32` of `x` stay distinct and
`(Xor32 x x) => 0` does not fire before lowering. After `lower` the AMD64 rules see
`MOVLQZX (ANDL t (NOTL (XORL t1 t2)))`, fold the right operand to `-1`, and then:

1. `(MOVLQZX (ANDLconst [c] x)) => (ANDLconst [c] x)` (AMD64.rules) removes the zero
   extension, because a 32-bit `ANDL` clears the upper half of its destination;
2. `(AND(Q|L)const [-1] x) => x` removes the `ANDL` itself.

What remains is the argument register, whose upper 32 bits are those of `x`. The
`lower` SSA dump shows the function reduced to `MakeResult v6` with `v6` the 64-bit
argument. This is exactly the interaction josharian described in #36897; randall77 and
cherrymui agreed it is unsound, and the issue was left unplanned for lack of a trigger.

## How it was found

The long alternative-compiler campaign (2026-11-06, seed 20261118, `core` suite, native
amd64): `gc-noopt` (go1.27.3 with `-N -l`) disagreed with the Lean oracle, gc, gccgo,
TinyGo and LLGo on two generated functions, `uint32(x) &^ (uint32(x) ^ uint32(x))` and
`(uint32(y) &^ 0) &^ (uint32(x) ^ uint32(x))`.
