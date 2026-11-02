<!-- Filed as golang/go#82786 on 2026-11-02 after human approval. -->
### Go version

go1.16 through go1.27.3 and master (a0c8470e). go1.15 is correct.

### Output of `go env` in your module/workspace:

GOOS=linux GOARCH=arm, run under qemu-arm 11.1.2.

### What did you do?

```go
package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func f() int {
	return bits.TrailingZeros64(uint64(uint16(bits.OnesCount16(16384))) &^ 16777217)
}

func main() { fmt.Println(f()) }
```

### What did you see happen?

`32`.

### What did you expect to see?

`64`: the argument is `1 &^ 0x1000001 == 0`. amd64, arm64, 386 and mipsle print `64`.

### Analysis

ARM.rules folds `MVNshiftRA` of a constant without the complement:

    (MVNshiftRA (MOVWconst [c]) [d]) => (MOVWconst [int32(c)>>uint64(d)])

while the LL and RL siblings use `^(...)`, and go1.15 had `^int64(int32(c)>>uint64(d))`; the `^` was
lost in the go1.16 conversion to typed AuxInts. Here the 32-bit decomposition of `Ctz64` lowers
`Com32(Zeromask(lo))` to `MVNshiftRA [31] lo`, and once `lo` folds to 0 during lowering the rule
returns 0 instead of -1, so the `+32` for the high word is dropped.

Restoring the complement fixes it; `go test -short cmd/compile/internal/ssa
cmd/compile/internal/test` and the codegen tests pass. I'll send the change via Gerrit.

Found with a metamorphic fuzzer (constant vs. run-time operands) under qemu.

Assisted by AI.
