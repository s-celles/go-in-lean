# JOIN-GUARD-CONSERVATIVE: `strings.Join` / `bytes.Join` report an overflow that does not occur

**Classification:** `go_discrepancy_reproduced`, severity **negligible**, potentially novel.
**Human review status:** pending. **No upstream action proposed**; see "Assessment".

## Expected behaviour

`Join` panics with "output length overflow" when the length of the result,
`len(sep)·(len(elems)-1) + Σ len(elems[i])`, does not fit in an `int`.
(Contract inferred from the panic message and the comment "Since we cannot
return an error on overflow, we should panic if the repeat will generate an
overflow" used for the sibling `Repeat`; `Join`'s doc comment says nothing
about overflow.)

## Actual behaviour

The separator guard (`src/strings/strings.go`, `src/bytes/bytes.go`, go1.25.5)
is `if len(sep) >= maxInt/(len(elems)-1) { panic(...) }`. Because of `>=` and
integer division it also fires when the exact length still fits.

* Lean (kernel-checked, `Go.Overflow.joinSep_not_exact`): with `k = 3`
  separators and `len(sep) = MaxInt/3 = 3074457345618258602`, the guard fires
  although `3·len(sep) = MaxInt − 1`. `Go.Overflow.joinSep_sound` proves the
  guard never *misses* a real overflow.
* Go (`go/tests/overflow_test.go`, `TestJoinGuardConservative`, go1.25.5
  darwin/arm64): `strings.Join([]string{"", "", "", ""}, sep)` with
  `len(sep) = MaxInt/3` (a string header built with `unsafe.String` over one
  byte; no memory is read) panics `strings: Join output length overflow`;
  `bytes.Join` likewise. Exact result length `MaxInt − 1`.

## Assessment

* Unreachable without `unsafe`: no real string can have length near `2^63`.
* Even with `unsafe`, the alternative to this panic is an attempt to allocate
  ~`2^63` bytes, i.e. a fatal (unrecoverable) out-of-memory error. The
  conservative guard yields a recoverable panic instead, which is arguably
  preferable. The only observable inaccuracy is the word "overflow".
* `Repeat` (`bits.Mul`-based guard) and `slices.Concat` (`size < 0` after
  each addition) are exact: proved `repeatPanics_iff`, `concatSize_spec`.

## Known-issue search

Web search (2026-11-01) found no golang/go issue about the `Join` guard;
related: golang/go#25709 (`Repeat` huge count), golang/go#16237 (`Repeat`
overflow, fixed Go 1.8).

## Reproduction

```sh
lake build GoInLean.Stdlib.Overflow
cd go && go test ./tests -run TestJoinGuardConservative -v
```

## Confidence

High that the behaviour is as described (proof + execution). High that it is
not a defect worth reporting; recorded for completeness and as a
demonstration that the pipeline separates "discrepancy" from "bug".
