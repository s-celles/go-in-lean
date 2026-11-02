<!-- Filed as https://github.com/golang/go/issues/82763 on 2026-11-02 (final text edited slightly). -->

**Title:** cmd/compile: wrong result for `((x >> c) & d) << e` with constant shift count c >= 1<<63

### Go version

go version go1.27.3 darwin/arm64; also go1.26.10, go1.25.5, and tip (go1.28-devel_babb75be); GOARCH=amd64 as well

### What did you do?

```go
package main

import "fmt"

//go:noinline
func f(x int64) int64 { return ((x >> (1 << 63)) & 3) << 1 }

//go:noinline
func g(x int64, n uint64) int64 { return ((x >> n) & 3) << 1 }

func main() {
	fmt.Println(f(-1), g(-1, 1<<63)) // want 6 6
}
```

### What did you see happen?

`0 6`

### What did you expect to see?

`6 6`. The spec says shift counts have no upper limit, so `-1 >> (1<<63)` is `-1`.

### Analysis

The generic rules under `// ((x >> c) & d) << e` in `_gen/generic.rules` choose between
`c >= e` and `c < e` with signed comparisons of the int64 AuxInts and compute `e-c` / `c-e`.
A count `c >= 1<<63` is a negative AuxInt, so the `c < e` branch rewrites the arithmetic
right shift into `x << (e-c)`. The same code reached through inlining
(`field(x, ^uint64(0), 3) << 1` with a non-inlined-shift helper) also returns a wrong value.
Unsigned operands are not affected, because `(Rsh64Ux64 _ (Const64 [c])) && uint64(c) >= 64`
folds the inner shift first.

Adding `c >= 0 && e >= 0` to the eight rules fixes it (patch attached; on tip it fixes the
reproducer and `cmd/compile/internal/{ssa,test}` and `test/codegen/shift.go` still pass); we
also checked the fixed rules for all widths with a bit-precise proof.

Assisted by AI.
