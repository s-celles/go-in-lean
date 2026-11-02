<!-- DRAFT for human review. Do not file without explicit approval. -->
### Go version

go1.26.10, go1.27.3 and master (go1.28-devel_babb75be). go1.25.5 is correct.

### Output of `go env` in your module/workspace:

GOOS=linux GOARCH=riscv64, run under qemu-riscv64 11.1.2.

### What did you do?

```go
package main

import "fmt"

//go:noinline
func f(x int8) int8 { return (x - (-x)) >> 8 }

//go:noinline
func g(x int16) int16 { return (x - (-x)) >> 16 }

func main() { fmt.Println(f(-1), g(-3)) }
```

### What did you see happen?

`0 0`. `f` compiles to `MOV $0, X10; RET`.

### What did you expect to see?

`-1 -1` (`int8(-2) >> 8` is -1). amd64, arm64 and go1.25.5 on riscv64 print `-1 -1`.

### Analysis

In the `lower` pass, `Rsh8x64 v (Const 63)` becomes `SRAI [63] (MOVBreg v)`, then
`(SRAI <t> [x] (MOVBreg y)) && x >= 8 => (SRAI [63] (SLLI <t> [56] y))` creates a 64-bit shift
typed `int8`. `x - (-x)` lowers to `ADD x x`, and the go1.26 rule
`(SLLI <t> [c] (ADD x x)) && c >= t.Size()*8-1 => (MOVDconst [0])` trusts the `int8` type and
folds the shift to 0, although `SRAI [63]` reads bit 63 of the 64-bit result.

Typing the inner shift as `typ.Int64` in the two `SRAI (MOV(B|H)reg)` rules fixes it (the sound
rule `(SLLI [c] (ADD x x)) => (SLLI [c+1] x)` then applies); `go test -short
cmd/compile/internal/ssa cmd/compile/internal/test` and the codegen tests pass. A bit-precise
model (Lean 4, bv_decide) of the rules confirms the analysis.

Found with a metamorphic fuzzer (constant vs. run-time shift counts) run under qemu.

Assisted by AI.
