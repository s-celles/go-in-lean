<!-- DRAFT for human review. Do not file without explicit approval. -->
### Go version

go1.21.13 through go1.27.3 and master (go1.28-devel_babb75be).

### Output of `go env` in your module/workspace:

GOARCH=arm64 (darwin/arm64 natively; linux/arm64 under qemu-aarch64 behaves the same).

### What did you do?

```go
package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func f(x, y int64) int64 {
	r := x >> 33
	if bits.OnesCount8(128) > 0 { // always true
		r = ^y
	}
	return r
}

func main() { fmt.Println(f(0, 2), f(5, 0)) }
```

### What did you see happen?

`3 1`. `f` compiles to `EOR $1, R1, R0; RET`.

### What did you expect to see?

`-3 -1`. amd64 prints `-3 -1`.

### Analysis

The select becomes `CSINV [GreaterEqual] (SRAconst [33] x) y flags`. The `OnesCount8` table load
folds to a constant during `lower`, so the flags become `FlagConstant` and

    (CSINV [cc] _ y flag) && ccARM64Eval(cc, flag) < 0 => (Not y)

fires. `Not` is the boolean negation and lowers to `XOR $1`, but `CSINV` needs the bitwise
complement: the rule should produce `(MVN y)` (as the sibling rules produce `(NEG y)` for CSNEG and
`(ADDconst [1] y)` for CSINC). With that change the program prints `-3 -1`, and `go test -short
cmd/compile/internal/ssa cmd/compile/internal/test` plus the codegen and fixedbugs tests pass.

Found with a metamorphic fuzzer (constant vs. run-time operands).

Assisted by AI.
