<!-- Filed as https://github.com/golang/go/issues/82767 on 2026-11-02. -->
**Title:** cmd/compile: wrong result for `(x >> c) >> d` on int16/int32 with huge constant counts (tip regression)

### Go version

go version go1.28-devel_babb75be darwin/arm64 (also GOARCH=amd64). go1.27.3 is correct.

### What did you do?

```go
package main

import "fmt"

func shr2(y int32, a, b uint64) int32 { return (y >> a) >> b }

//go:noinline
func f(y int32) int32 { return shr2(y, 1, 1<<62) }

func main() { fmt.Println(f(2), f(-5)) } // want 0 -1
```

### What did you see happen?

`1 -3` on tip; `0 -1` with go1.27.3.

### Analysis

The shift-composition rules in `_gen/generic.rules`, e.g.
`(Rsh32x64 <t> (Rsh32x64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Rsh32x64 x (Const64 <t> [c+d]))`,
type the combined count with the shifted value's type `<t>` (int32), the same problem as
#81868 but in rules CL 795240 did not touch (8/16/32-bit Lsh/Rsh/RshU composition). On tip,
`InitLimit` now ends with `PropagateUnsignedSignedRelationship(v.Type.Size()*8)`, which
truncates the 64-bit constant `1<<62 + 1` to 32 bits (1); prove then marks the shift bounded
and the lowered shift masks the count. `GOSSAFUNC` shows `Const64 <int32> [4611686018427387905]`
after opt and `Rsh32x64 [true]` after prove.

Using `Const64 <typ.UInt64>` in those nine rules fixes it (patch below; on tip the
reproducer and a fuzzing corpus are correct and `cmd/compile/internal/{ssa,test}` and
`test/codegen/shift.go` pass).

Assisted by AI.
