<!-- Filed as golang/go#82839 on 2026-11-03 after maintainer approval. -->
### Go version

go1.26.6 through go1.26.10, go1.27.3 and master (2885c994). go1.26.5 is correct for this program.

### Output of `go env` in your module/workspace:

Any GOARCH; reproduced on darwin/arm64, linux/amd64 and linux/arm.

### What did you do?

```go
package main

import "fmt"

var sink int

//go:noinline
func f(x uint8) {
	if int32(int16(x)-513) < -536870911 {
		sink = 1
	}
}

func main() {
	f(0)
	fmt.Println(sink)
}
```

### What did you see happen?

`1`.

### What did you expect to see?

`0`: `int16(x)-513` is in [-513, -258], so the condition is always false.

### Analysis

With `-d=ssa/prove/debug=2`: `x+d >= w; x:v64 ... delta:-513 w:-536870911 d:signed`, then
`Proved Less32`. In `factsTable.update`, "look through value-preserving extensions" repeats the fact
`SignExt16to32(v65) >= Const32 [-536870911]` on the 16-bit `v65 = Add16 v64 (Const16 [-513])` with
the same 32-bit constant; the "x+delta > w" step then computes `int16(w.AuxInt) - int16(delta)`,
and `int16(-536870911)` is 1, so it derives `v64 >= 514` and declares the other branch impossible.

The look-through is only meaningful when the constant fits in the narrow type. Carrying the fact
over only in that case fixes the program; the prove, loopbce, checkbce, codegen and fixedbugs tests
pass. The same code is present since at least go1.24 (`if int32(int16(x)-513) < int32(u) { return 1 }`
with `u := uint32(0xE0000001)` is wrong on go1.24.13 .. go1.26.x); go1.26.6's backport of "fix time
traveling proofs in prove" (#80619) made the form above reach it. I'll send the change via Gerrit.

Found with a metamorphic fuzzer (constant vs. run-time operands).

Assisted by AI.
