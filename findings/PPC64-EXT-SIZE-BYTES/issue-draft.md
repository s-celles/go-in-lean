<!-- Filed as golang/go#82775 on 2026-11-02 after human approval. -->
### Go version

go1.21.13 through go1.27.3 and master (go1.28-devel_babb75be).

### Output of `go env` in your module/workspace:

GOOS=linux GOARCH=ppc64le (also ppc64; GOPPC64=power8 and power9), run under qemu-user 11.1.2.

### What did you do?

```go
package main

import "fmt"

//go:noinline
func f(x int32) int32 { return int32(int16(x >> 1)) }

//go:noinline
func g(x uint32) uint32 { return uint32(uint16(x >> 1)) }

func main() { fmt.Println(f(-1<<31), g(1<<31)) }
```

### What did you see happen?

`-1073741824 1073741824`. `f` compiles to `SRAW $1, R3, R3`.

### What did you expect to see?

`0 0` (`int16(-1<<30)` and `uint16(1<<30)` are 0). Other architectures print `0 0`.

### Analysis

`PPC64.rules` has:

    (MOV(WZ|W)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() <= 32 => (S(R|RA)Wconst [c] x)
    (MOV(HZ|H)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() <= 16 => (S(R|RA)Wconst [c] x)
    (MOV(BZ|B)reg (S(R|RA)Wconst [c] x)) && x.Type.Size() == 8 => (S(R|RA)Wconst [c] x)

`Type.Size()` is in bytes, so the half-word rule always fires and removes the 16-bit extension
of a 32-bit right shift (`MOVHreg (SRAWconst [1] x)` -> `SRAWconst [1] x`), and the byte rule
fires for 64-bit operands. (The word rule is harmless since SRW/SRAW extend their result.)

Since a 16-bit value's register is not necessarily extended, even `Size() <= 2` would not be
enough; deleting the half-word and byte rules (the pattern-based rules just above them still
handle explicitly extended operands) fixes the program, and `go test -short
cmd/compile/internal/ssa cmd/compile/internal/test` plus the codegen and fixedbugs tests pass.
A bit-precise model (Lean 4, bv_decide) of the rules confirms the analysis.

Found with a metamorphic fuzzer run under qemu with GOPPC64=power9.

Assisted by AI.
