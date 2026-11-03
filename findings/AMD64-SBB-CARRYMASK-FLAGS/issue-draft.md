<!-- Filed as golang/go#82825 on 2026-11-03 after human approval.
Security assessment: ordinary miscompilation, no memory-safety impact; see
go-in-lean-private findings/AMD64-SBB-CARRYMASK-FLAGS/security-assessment.md. -->

### Go version

go1.24.13 through go1.27.3 and master (go1.28-devel_2b74366d). go1.21.13 and older not
tested; the annotation has been missing since the carry-mask ops were introduced.

### Output of `go env` in your module/workspace:

```
GOARCH=amd64
GOOS=linux
GOAMD64=v1   # v2 and v3 behave the same
```

### What did you do?

```go
package main

import "fmt"

//go:noinline
func f(x, y uint64) uint64 {
	r := x << y
	eq := uint64(0)
	if y == 64 {
		eq = 1
	}
	return r + eq
}

func main() { fmt.Println(f(1, 64), f(1, 63), f(1, 65)) }
```

### What did you see happen?

```
1 9223372036854775808 1
```

`f(1, 65)` returns 1.

### What did you expect to see?

```
1 9223372036854775808 0
```

`1 << 65` is 0 and `65 == 64` is false.

### More affected shapes

All on go1.27.3 and master `2b74366d`, linux/amd64: `y != 64` (wrong the other way, the
compiled condition is `y < 64`), unsigned and signed `x >> y` combined with `y == 64`
(`int64(-1) >> y` with `y == 64` returns 0 instead of -1 for y = 65), and the 32-bit form
`x << y` with `y == 32`. Source order matters: when the `SETcc` happens to be scheduled
before the `SBB` the result is correct.

On linux/386 (go1.24.13 .. go1.27.3) the same missing annotation miscompiles a decomposed
64-bit comparison whose high-word `CMP` is shared with a shift's count saturation:

```go
//go:noinline
func d(x int16) int16 {
	r := int16(-2047) << uint64(uint64(x))
	if uint64(x) <= 8589934591 { // 0x1FFFFFFFF; false for negative x
		r = int16(x) &^ 3
	}
	return r
}
// d(-1) is -4 on linux/386; the spec says 0.
// Passing the bound as a run-time parameter compiles correctly.
```

(The `-d=ssa/all/dump` phase dumps are correct through `late_opt`; the wrong condition
appears once `lower` produces the two flag consumers and the schedule places the `SBB`
between the `CMP` and the `SETEQ`.)

### Analysis

`SBBQcarrymask` and `SBBLcarrymask` (`_gen/AMD64Ops.go`) and `SBBLcarrymask`
(`_gen/386Ops.go`) expand to an `SBB` instruction, which writes the flags register, but
their OpcodeTable entries lack `clobberFlags: true`. The lowering of an unbounded shift
emits `CMPQconst [64] y` feeding the count mask (`SBBQcarrymask`); when the program also
tests the count against the width, the same flags feed a `SETcc`. `flagalloc` believes the
flags stay live across the `SBB`, does not regenerate them for the second consumer, and the
assembler emits the `SBB` between the `CMP` and the `SETEQ`, which then reads the `SBB`'s
flags. For `f` the compiled condition for `y == 64` is `y >= 64`:

```
SHLQ  CX, AX
CMPQ  CX, $64
SBBQ  DX, DX      // writes the flags
SETEQ BL          // reads the SBBQ's flags, not the CMPQ's
ANDQ  DX, AX
```

The borrow-taking forms `SBBQ`/`SBBL`/`SBBLconst` carry `clobberFlags: true`; only the
carry-mask forms are missing it. This is the x86 instance of the class of golang/go#81842
(ppc64x `DIVD` clobbers CR0 unmarked) and golang/go#21080 (s390x `MOVDaddr`).

Compiler-inserted bounds checks are not affected: they compare an index against a
run-time length, a different comparison from the width-constant one the defect needs, and
branch control values are handled separately by `flagalloc`. No out-of-bounds access was
observed; the impact is wrong boolean results.

We have a small patch that makes the reproducers print the spec results on amd64 and 386
with the `ssa`, `prove`/`loopbce`/`checkbce`/`codegen` and `fixedbugs` tests still
passing; we will send it as a CL.

Found with the metamorphic `--late` fuzzer campaign (constants materialised from read-only
data during lowering) on 386, then root-caused on amd64 from the phase dumps; the amd64
shapes above follow the flag-clobbering mechanism directly.

Assisted by AI.
