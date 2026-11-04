<!-- Posted 2026-11-04: https://github.com/golang/go/issues/80577#issuecomment-6643325028 -->

The same restore-by-type problem has a much smaller reproducer on current tip
`ede4e4ff00`, and it also affects arm64:

```go
package main

import "fmt"

//go:noinline
func id(x int64) int64 { return x }

//go:noinline
func f(y int8) int64 {
	v := int16(uint16(y))
	z := id(int64(v))
	if v >= 9 {
		return z + 1000
	}
	return z - 1000
}

func main() { fmt.Println(f(-1)) }
```

The specified result is `-1001`. It prints `999` on arm64, ppc64le and ppc64,
and `-1001` on amd64, 386, arm, mipsle, mips64le, riscv64, s390x and loong64.
No artificial register pressure is needed: keeping `v` live across the call is
enough. The failure is present from at least go1.21.13 through go1.27.3 and tip.

On arm64, `v` starts sign-extended but carries the unsigned `uint16` SSA type:

```text
SXTB  R0, R1
MOVH  R1, 22(RSP)
CALL  main.id(SB)
MOVHU 22(RSP), R1
CMPW  $9, R1
```

The zero-extending restore makes the signed comparison see 65535 and take the
wrong branch. PPC64 has the analogous `EXTSB` / `MOVH` / `MOVHZ` sequence. A
targeted matrix also finds the same problem for
`int32(uint32(int16(-1)))` on ppc64 and ppc64le.

The arm64 elimination is the unconditional late-lower rule
`(MOVHreg x:(MOVBreg _)) => (MOVDreg x)`. An experimental guard on the six
signed-over-signed double-extension folds (`x.Type.Size() == 8 ||
x.Type.IsSigned()`) fixes the reproducer and all 84 targeted width/pressure
cases; the targeted compiler tests pass. I expect the central restore-contract
work already discussed on this issue to be preferable to another local spelling
of the condition.

Assisted by AI.
