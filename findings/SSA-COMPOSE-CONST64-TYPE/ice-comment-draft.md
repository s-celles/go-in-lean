<!-- Draft for https://github.com/golang/go/issues/82767; not posted. -->
There is also a compiler-crash boundary of the same mistyped-`Const64` bug on current tip
(`go1.28-devel_67219752`, linux/amd64):

```go
package p

func f(y int32) int32 {
	return (y >> 1) >> (uint32(1) << 31)
}
```

`go tool compile repro.go` fails with:

```text
internal compiler error: 'f': panic during prove while compiling f:
runtime error: negative shift amount
cmd/compile/internal/ssacompile.(*factsTable).flowLimit
    src/cmd/compile/internal/ssacompile/prove.go:1518
```

After `opt`, the composed shift is:

```text
Const64 <int32> [2147483649]
Rsh32x64 <int32> y (Const64 <int32> [2147483649])
```

`InitLimit` intersects the positive 64-bit constant with its signed 32-bit interpretation and
produces an unsatisfiable range (`Min=2147483649`, `Max=-2147483647`). `flowLimit` checks only
`Min >= 0`, then evaluates `a.Min >> b.Max`, which panics because `b.Max` is negative.

Patchset 1 of CL 857342 fixes this reproducer unchanged on top of tip 67219752, and the targeted
`cmd/compile/internal/ssa` and `cmd/compile/internal/test` suites pass. It may be worth adding this
smaller compile-crash case to `test/fixedbugs/issue82767.go` alongside the wrong-code cases.

Assisted by AI.
