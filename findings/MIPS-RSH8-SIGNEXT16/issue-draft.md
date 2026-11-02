<!-- Filed as golang/go#82772 on 2026-11-02 after human approval. -->
### Go version

go1.27.3 and master (go1.28-devel_babb75be); the rules are unchanged since go1.8.

### Output of `go env` in your module/workspace:

GOOS=linux GOARCH=mipsle (also mips); built on linux/amd64 and darwin/arm64, run under qemu-user 11.1.2.

### What did you do?

```go
package main

import "fmt"

//go:noinline
func mulShr8(x, k int8, s uint64) int8 { return (x * k) >> s }

//go:noinline
func addShr8(x, k int8, s uint32) int8 { return (x + k) >> s }

func main() {
	fmt.Println(mulShr8(127, -15, 8), mulShr8(127, -15, 3), addShr8(127, 1, 8))
}
```

`GOOS=linux GOARCH=mipsle go build && qemu-mipsel ./prog`

### What did you see happen?

`-8 17 0`

### What did you expect to see?

`-1 -15 -1` (`int8(127 * -15)` is -113, `int8(127 + 1)` is -128). GOARCH=386, arm and mips64le print the expected values.

### Analysis

`src/cmd/compile/internal/ssa/_gen/MIPS.rules` lowers `Rsh8x32`, `Rsh8x16` and `Rsh8x8` with
`(SRA (SignExt16to32 x) ...)`. `x` is an 8-bit value whose register may hold garbage above bit 7
(here the raw `MUL`/`ADDU` result), so the sign must come from bit 7: `SignExt8to32`, as in every
other signed 8-bit rule of the file and in `MIPS64.rules`. The assembly shows `MUL; MOVH; …; SRA`.

Replacing `SignExt16to32` with `SignExt8to32` in the three rules (and regenerating) fixes the
program; `go test -short cmd/compile/internal/ssa cmd/compile/internal/test` passes. A bit-precise
model of the lowering (Lean 4, bv_decide) proves the corrected rules for all register values and
counts.

Found with a metamorphic fuzzer (constant vs. run-time shift counts) run under qemu.

Assisted by AI.
