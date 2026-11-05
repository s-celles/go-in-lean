### Go version

go version go1.26.10 linux/arm64 (also GOARCH=loong64). go1.27.3 and tip are correct; amd64 and the other architectures are correct on go1.26.10.

### Output of `go env` in your module/workspace:

```shell
Cross-compiled with GOOS=linux GOARCH=arm64 (and loong64) from linux/amd64, run under qemu-user 11.1.2.
```

### What did you do?

```go
package main

import (
	"fmt"
	"math/bits"
)

//go:noinline
func f(x, y uint64) uint64 { return x << bits.Reverse64(y) }

//go:noinline
func g(x uint64, y uint) uint64 { return x >> bits.Reverse(y) }

func main() {
	// Reverse64(3) = 0xC000000000000000, an unsigned count >= 64: want 0 0
	fmt.Println(f(3, 3), g(3, 3))
}
```

### What did you see happen?

```
panic: runtime error: negative shift amount
```

on go1.26.10 for GOARCH=arm64 and GOARCH=loong64.

### What did you expect to see?

`0 0`: the count is a `uint64` (`uint`), so it cannot be negative, and a count >= 64 gives 0.

### Analysis

On go1.26, the `math/bits` `Reverse`, `Reverse8/16/32/64` intrinsics (registered for `sys.ARM64, sys.Loong64`) build their result with type `types.Types[types.TINT]`:

```go
return s.newValue1(ssa.OpBitRev64, types.Types[types.TINT], args[0])
```

When that value is used as a shift count, `ssagen` sees a signed count type and inserts the `0 <= count` check that calls `runtime.panicshift` (`TBNZ $63, R1` on arm64), so any reversed value with the top bit set panics.

On master and go1.27 this was fixed by 819c53c25f (CL 731300, "cmd/compile: ensure ops have the expected argument widths"), which changes these result types to `TUINT64`/`TUINT`. That commit says "I don't think there is a triggerable bug here"; the program above seems to be one, so a 1.26 backport of that part may be warranted.

Found by a differential campaign (gc 1.26/1.27/tip, TinyGo and gc `-N -l` under qemu, checked against an executable model of the spec): only go1.26.10 on arm64 panicked, in a generated program whose count was `bits.Reverse64(bits.RotateLeft64(7, 63))`.

This was found and reduced on my own time and hardware, as part of a personal project ([go-in-lean](https://github.com/s-celles/go-in-lean)), out of interest in free software. My means let me report defects with a reproducer and an analysis, but not offer and maintain fixes for every project concerned, so I am not planning a CL for this one; I am happy to answer questions about the reproducer. The analysis was AI-assisted and may well be wrong, or partly debatable, despite my checks: if this report is mistaken or questionable in any part, please say so, courteously, and I will correct or close it. Assisted by AI.
