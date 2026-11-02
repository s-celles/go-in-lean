<!-- Filed as golang/go#82776 on 2026-11-02 after human approval. -->
### Go version

go1.21.13 through go1.27.3 and master (go1.28-devel_babb75be).

### Output of `go env` in your module/workspace:

GOOS=linux GOARCH=mipsle (also mips), run under qemu-user 11.1.2.

### What did you do?

```go
package main

import "fmt"

//go:noinline
func f(x, y int8) int8 { return (x >> 7) >> (uint64(y) | 0xFFFFFFFF) }

func main() { fmt.Println(f(127, -128)) }
```

### What did you see happen?

`1`. `f` compiles to `SLL $24; SRA $30`, i.e. `x >> 6`.

### What did you expect to see?

`0` (`127 >> 7` is 0). 386 and arm print `0`.

### Analysis

In `late_opt`, after `dec64`, the generic rule
`(Rsh8x64 (Rsh8x64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Rsh8x64 x (Const64 <t> [c+d]))`
merges the two shifts into `Rsh8x64 x (Const64 [4294967302])` (7 + 0xFFFFFFFF). `MIPS.rules`
then lowers constant 64-bit counts with conditions on `uint32(c)`:

    (Rsh8x64 x (Const64 [c])) && uint32(c) < 8 => (SRAconst (SLLconst <typ.UInt32> x [24]) [int32(c+24)])

so the count is taken as 6. `ARM.rules` and `386.rules` use `uint64(c)` in the same rules.
Replacing `uint32(c)` with `uint64(c)` in the 18 constant-count shift rules of `MIPS.rules` fixes
the program; `go test -short cmd/compile/internal/ssa cmd/compile/internal/test` and the codegen
and fixedbugs tests pass. (Separate from #82772, which is about `Rsh8x32` with a variable count.)

Found with a metamorphic fuzzer run under qemu.

Assisted by AI.
