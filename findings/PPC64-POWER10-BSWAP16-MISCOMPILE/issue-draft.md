<!-- Draft golang/go issue for review. Same style as the public #82772-#82777. Not yet filed. -->
### Go version

go1.27.3 and master (confirmed a0c8470e, 2026-11-02). go1.26.10 and earlier are correct.

### Output of `go env` in your module/workspace:

GOOS=linux GOARCH=ppc64le (also ppc64), GOPPC64=power10; run under qemu-ppc64le 11.1.2 -cpu power10.

### What did you do?

```go
package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func f(k uint16, y, z int16) int16 {
	r := ^int16(bits.ReverseBytes16(k))
	if y <= z {
		r = 7
	}
	return r
}

func main() { fmt.Println(f(0x0400, 5, 1)) }
```

`GOPPC64=power10 GOOS=linux GOARCH=ppc64le go build && qemu-ppc64le -cpu power10 ./prog`

### What did you see happen?

`7`.

### What did you expect to see?

`-5`. `5 <= 1` is false, so `r` stays `^bits.ReverseBytes16(0x0400) == ^0x0004 == -5`.
GOPPC64=power9, amd64, arm64 and go1.26 print `-5`.

### Analysis

The Power10 `ReverseBytes16` intrinsic (`ssagen/intrinsics.go`, `cfg.goppc64 >= 10`) builds
`OpBswap16` with result type `types.Types[types.TUINT]` (64-bit unsigned); the loong64 and riscv64
intrinsics use `types.Types[types.TUINT16]`. The value is a 16-bit byte reversal typed as a 64-bit
unsigned, so prove gets a false fact about `^int16(ReverseBytes16(k))` (effectively that its sign
bit is clear) and folds the comparison, producing the wrong value. Typing the Power10 `OpBswap16`
as `TUINT16` fixes it; `go test -short cmd/compile/internal/ssa cmd/compile/internal/test` and the
codegen tests pass. Same class as #82767.

(The fix goes via Gerrit, not pasted here.)

Assisted by AI.
