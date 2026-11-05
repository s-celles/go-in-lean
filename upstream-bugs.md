# Upstream bugs found outside the Go toolchain

Defects found in third-party projects while running go-in-lean harnesses.
Go compiler issues are tracked in `docs/upstream-status.md`, not here.
Every entry needs human review before an issue is filed; the status line of
each entry says whether and where it was reported.

These reports are made on personal time and hardware, out of interest in free
software. They come with a reduced reproducer and an analysis, but not with a
pull request: fixing the defect is the maintainers' responsibility. Every
report ends with this paragraph, adapted if needed:

> This was found and reduced on my own time and hardware, as part of a personal
> project ([go-in-lean](https://github.com/s-celles/go-in-lean)), out of
> interest in free software. My means let me report defects with a reproducer
> and an analysis, but not offer and maintain fixes for every project
> concerned, so I am not planning a pull request for this one; I am happy to
> answer questions about the reproducer. The analysis was AI-assisted and may
> well be wrong, or partly debatable, despite my checks: if this report is
> mistaken or questionable in any part, please say so, courteously, and I will
> correct or close it. Assisted by AI.

## Yaegi: shift count truncated to the operand width in an assignment

- **Project**: [traefik/yaegi](https://github.com/traefik/yaegi), Go interpreter.
- **Version**: 0.16.1 (nixpkgs) and 0.16.3 (released 2026-11-05, tag
  `e622b4e3a12c` = master HEAD that day); both reproduce the two symptoms.
- **Found by**: `scripts/alt_compiler_diff.py`, core suite, seed 20261105,
  case `core-20261105-00149` (loop function `l0`); the Lean oracle, gc,
  gccgo, TinyGo and LLGo all agree on the specified result.
- **Status**: reported as [traefik/yaegi#1750](https://github.com/traefik/yaegi/issues/1750)
  (2026-11-05, from the `s-celles-bot` account), after checking the tracker:
  #1661 is a distinct untyped-constant shift overflow, and the 0.16.3 fixes for
  untyped binary expressions (`e686f5576`, `1e3e91df8`) do not cover it.

When the result of a shift is *assigned* to an existing variable and the count
is an expression (not a plain identifier), the count is converted to the type
of the shifted operand before shifting. A count of `1<<32 | 1` applied to a
`uint32` therefore acts as 1, and `256 | 3` applied to an `int8` acts as 3. The
Go specification has no such truncation: a count greater than or equal to the
width yields 0 (or the sign fill for a signed right shift). The `:=` form and a
plain-identifier count are evaluated correctly.

```go
package main

import "fmt"

func main() {
	var x, r uint32 = 170, 0
	k := uint64(1<<32 | 1)
	r = x >> (k + 0)
	fmt.Println(r) // spec, gc, gccgo: 0; yaegi 0.16.1: 85

	var a, b int8 = 1, 0
	n := uint64(256 | 3)
	b = a << (n + 0)
	fmt.Println(b) // spec, gc, gccgo: 0; yaegi 0.16.1: 8

	c := x >> (k + 0)
	fmt.Println(c) // 0 everywhere
	r = x >> k
	fmt.Println(r) // 0 everywhere
}
```

A second symptom, probably of the same type propagation (the count expression
receives the type of the shifted operand): when the count contains a
parenthesised binary sub-expression, the program is rejected while loading,
although it is valid Go (gc and gccgo accept it and print 8). Found as a
`run_error` in case `core-20261105-00481`.

```go
package main

import "fmt"

func main() {
	var r, s int16 = 0, 64
	k := uint64(3)
	r = s >> ((k - k) ^ k)
	fmt.Println(r)
	// yaegi 0.16.1: run: main.go:8:6: invalid operation: mismatched types int16 and uint64
}
```

Campaign extent (seed 20261105): 8 of the 1,500 `core` programs and 6 of the
500 `bits` programs give a wrong Yaegi output, and all 14 become correct once
every `v = <expr with a shift>`
assignment is rewritten as `{ tmp := <expr>; v = tmp }` (`triage_yaegi.py`
in the GEEKR9 run directory); 1 program is rejected as above.

