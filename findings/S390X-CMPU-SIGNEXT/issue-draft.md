<!-- Filed as golang/go#82774 on 2026-11-02 after human approval. -->
### Go version

go1.26.10, go1.27.3 and master (go1.28-devel_babb75be). go1.25.5 is correct.

### Output of `go env` in your module/workspace:

GOOS=linux GOARCH=s390x, run under qemu-s390x 11.1.2.

### What did you do?

```go
package main

import "fmt"

//go:noinline
func f(y int8) bool { return uint64(y) < 0xFFFFFFFF }

//go:noinline
func g(y int16) bool { return uint64(y) <= 0xFFFFFFF0 }

func main() { fmt.Println(f(-128), g(-20)) }
```

### What did you see happen?

`true true`. `f` compiles to `MOVB R2, R0; CMPWU R0, $4294967295; ...`.

### What did you expect to see?

`false false`: `uint64(int8(-128))` is `0xFFFFFFFFFFFFFF80`. amd64 and go1.25.5 on s390x print `false false`.

### Analysis

`S390X.rules` narrows 64-bit compares of extended values:

    (CM(P|P|PU|PU)const x:(MOV(H|HZ|H|HZ)reg _) [c]) => (CMP(W|W|WU|WU)const x [c])
    (CM(P|P|PU|PU)const x:(MOV(B|BZ|B|BZ)reg _) [c]) => (CMP(W|W|WU|WU)const x [c])

The `(CMPUconst x:(MOV(H|B)reg _) [c]) => (CMPWUconst x [c])` instance is not valid: a negative
sign-extended value is larger than any zero-extended 32-bit immediate in a 64-bit unsigned
compare, but its low 32 bits can be smaller. The other three instances are fine. The rule is
old; with go1.26 the argument arrives in a register, so the `MOVBreg` is no longer folded into a
sign-extending load and the rule fires.

Restricting that instance to `c >= 0` (immediate below 2^31) fixes the program; `go test -short
cmd/compile/internal/ssa cmd/compile/internal/test` and the codegen tests pass. A bit-precise
model (Lean 4, bv_decide) proves the restricted rule and the three other instances.

Found with a metamorphic fuzzer run under qemu.

Assisted by AI.
