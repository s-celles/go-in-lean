<!-- DRAFT follow-up comment for golang/go#82767. Not posted. -->
Additional data: the counts do not need to be huge. The combined count is truncated to the
width of the shifted type, so for int8 any pair of constant counts whose sum is close to a
multiple of 256 is enough:

```go
func shr8(y int8, a, b uint) int8 { return (y >> a) >> b }

//go:noinline
func f(y int8) int8 { return shr8(y, 128, 128) }

//go:noinline
func g(y int8) int8 { return shr8(y, 100, 157) }
```

On tip `f(100)` is 100, `f(-7)` is -7 and `g(100)` is 50; go1.27.3 gives 0, -1 and 0.
For int16, `(y >> 40000) >> 25537` returns `y >> 1`. The patch in the description fixes
these as well, and it also fixed every failure of a second fuzzing run on tip with
GOARCH=amd64 (e.g. `(x >> 256) >> 256` on int8).

Assisted by AI.
