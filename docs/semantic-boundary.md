# Semantic boundary (Phase 1)

This document fixes *what* of Go is modelled in Lean, *how*, under which
assumptions, and what is deliberately left out. Everything a theorem in this
repository says about Go is conditional on this document.

## Pinned versions

| Component | Version | Identifier |
|---|---|---|
| Go toolchain | go1.25.5 (darwin/arm64 locally, linux/amd64 in CI) | `go/.go-version`; GOROOT `VERSION`: `go1.25.5`, time 2025-11-26T02:01:51Z; Homebrew formula commit `c6069d2a943b71b0a90d91fc1ac93cb9c1634dcc` |
| Go sources modelled | `src/math/bits/bits.go` sha256 `0956e3586b4cf3f4605382523e55c018d58924bc688982431d6b7cda99d10ecd`; `src/math/bits/bits_tables.go` sha256 `c4cb4a05dab6d395d9d51720893a42f0a9d1cdf8a0c2383d87268e49acb73f7f`; `src/cmd/compile/internal/ssa/_gen/generic.rules` sha256 `d3be070342f2579f6e51814a572cf31282f53b8cff001dd640f1a2cc0eea1ae8` | checked by `scripts/gen_bits_tables.py --check` (tables) |
| Lean | `leanprover/lean4:v4.35.0` | `lean-toolchain` |
| Lake dependencies | none (no Mathlib, no Batteries) | `lakefile.toml` |
| Go specification | The Go Programming Language Specification, language version go1.25 | https://go.dev/ref/spec |
| Target architectures | 64-bit (`amd64`, `arm64`): `int`/`uint`/`uintptr` are 64 bits | assumption A1 |

## Assumptions

* **A1 (word size).** `int` and `uint` are 64-bit. Go only guarantees at
  least 32 bits (spec, "Numeric types": implementation-specific sizes).
  Every theorem mentioning `Go.int`/`Go.uint` is a theorem about 64-bit
  targets. `math/bits.UintSize` is therefore 64 in the model.
* **A2 (two's complement).** Signed values are two's-complement bit
  patterns. This is what the spec prescribes for overflow ("the result is
  truncated … wraps around") and for conversions ("sign extended to implicit
  infinite precision … then truncated").
* **A3 (panics as values).** Run-time panics are modelled as `Except Panic`
  errors; no recovery, no deferred functions. Only the panics that can occur
  in the modelled subset exist in the `Panic` type (divide, overflow,
  negative shift, index out of range, string message).
* **A4 (portable code path).** The model transliterates the *pure Go*
  bodies in `src/math/bits/bits.go`. The compiler intrinsifies several of
  these functions on amd64/arm64 (`bits.go` header comment). Theorems are
  about the portable code; the differential vectors (`scripts/check.sh`
  step 6) and the Go tests run on the compiled binary and therefore exercise
  the intrinsic where one exists. A disagreement between the two shows up
  there, not in a proof. Example: `bits.Add64(MaxUint64, MaxUint64, 2)` is
  `(MaxUint64, 1)` with the arm64 intrinsic and `(0, 1)` with the pure-Go
  formula; both are out of contract (golang/go#54255) and the test
  `TestAdd64CarryTwoIsOutOfContract` records this.
* **A5 (no concurrency, no heap).** Only pure, deterministic, single-threaded
  functions are modelled. No goroutines, channels, pointers, maps, interfaces,
  method dispatch, reflection, floating point, or strings/UTF-8.
* **A6 (operator precedence).** Go's binary-operator precedence has one
  level for `* / % << >> & &^` and one for `+ - | ^`; Lean 4's `>>>`, `+`,
  `&&&`, `^^^`, `|||` all have different precedences. Models are therefore
  written fully parenthesised. The proofs caught the first draft's violation
  of this rule (see `targets/properties.yaml`, BITS-TZ-16 history).

## Modelled features

### Fixed-width integers (`GoInLean/Semantics/Int.lean`)

| Go feature | Spec clause | Lean representation | Validation | Differences / omissions |
|---|---|---|---|---|
| `uintN`, `intN` for N ∈ {8,16,32,64}; `uint`, `int` (A1) | Numeric types | `BitVec N`; signedness is a property of the operation | `Semantics/Validation.lean` (exhaustive at 8 bits by `decide`) | `uintptr`, untyped constants and constant expressions are not modelled: Go constant arithmetic is arbitrary precision at compile time; literals in the models are written with their Go run-time type |
| `+ - *` | Integer overflow: "wraps around" | core `BitVec` `+ - *` (mod 2^N) | `Validation.lean`, vectors | none |
| `/`, `%` unsigned | Integer operators | `Go.divU`, `Go.remU`: `Except` error when divisor is 0, else core `/`, `%` | `∀ x : uint8, divU x 0 = error` by `decide`; `udiv_umod_identity` by `bv_decide` | Lean's bare `x / 0 = 0` is never relied on by a model |
| `/`, `%` signed | "truncated division"; `x / -1 = x` for the most negative value | `Go.divS`, `Go.remS` via core `sdiv`, `srem` | `(-7)/2 = -3`, `(-7)%2 = -1`, `MinInt8 / -1 = MinInt8`, `MinInt8 % -1 = 0` by `decide`; `sdiv_srem_identity` by `bv_decide` | `BitVec.smod` (floor) is never used |
| `<<`, `>>` with unsigned count | "no upper limit on the shift count"; shifts by ≥ width give 0 or the sign bit | `Go.shl`, `Go.shrU`, `Go.shrS` (core `<<<`, `>>>`, `sshiftRight` with `Nat` count) | `5<<10 = 0`, `5>>10 = 0`, `(-1)>>10 = -1` at 8 bits by `decide`; a Go probe program printed the same | Shift count of type `int` with a negative value panics in Go 1.13+: `Go.shlSigned`/`shrUSigned` return `negativeShift`; models in this repo only use unsigned counts, as `math/bits` does |
| Conversions between integer types | Conversions: zero-extend unsigned, sign-extend signed, then truncate | `Go.convU v x = x.setWidth v`, `Go.convS v x = x.signExtend v` | `uint8(300) = 44`, `int8(uint8(200)) = -56`, `uint64(int8(-1)) = MaxUint64` by `decide` | Float↔int conversions are not modelled (implementation-defined when out of range) |
| Comparisons | Comparison operators | `<`, `≤` (unsigned), `slt`, `sle` (signed) | by construction | none |
| `&^` | Arithmetic operators | `Go.andNot` | by construction | none |
| `math.MaxInt` | constants | `Go.maxInt = 2^63 - 1` (A1) | `decide` | 32-bit targets excluded by A1 |

### `math/bits` (`GoInLean/Stdlib/Bits.lean`)

All functions of `bits.go` are transliterated. `Len`, `LeadingZeros`,
`TrailingZeros`, `OnesCount`, `RotateLeft`, `Reverse`, `ReverseBytes`, `Add`,
`Sub`, `Mul`, `Div`, `Rem` on `uint` are, under A1, definitional aliases of
their 64-bit versions (in Go the `UintSize == 32` branch is dead code on
64-bit targets).

Specific modelling decisions:

* Lookup tables (`len8tab`, `ntz8tab`, `pop8tab`, `rev8tab`, the two de
  Bruijn tables) are generated byte-for-byte from the Go sources by
  `scripts/gen_bits_tables.py` into `Stdlib/BitsTables.lean`, together with a
  bit-blastable function version and a kernel-checked equality for every
  in-range index. Go indexes the tables with an unsigned value that is
  always `< len(table)`; `Go.Bits.tab` returns 0 outside the table (Go would
  panic). Proofs discharge the in-range side condition at every call site
  (`tab_lt`), so the out-of-range value never matters.
* `Mul64` is `(mulhiGeneric 32 x y, x * y)` where `mulhiGeneric h` is the
  schoolbook high-half algorithm for an arbitrary half-width `h`. The Go
  function is the `h = 32` instance; the algorithm is proved at `h = 4`.
* `Div64` is `divGeneric 32`, the Knuth algorithm for an arbitrary half-width,
  with (i) `LeadingZeros64(y)` replaced by the oracle `clzW y`, proved equal
  to the Go function (`LeadingZeros64_eq_clzW`), and (ii) the two correction
  `for` loops written with fuel 8 (Knuth's bound is 2 iterations). Panic
  conditions are proved for every `h`; functional correctness is proved for
  the `hi = 0` fast path at width 8 and for whatever `targets/properties.yaml`
  records under `BITS-DIV-8`.
* `Rem64`'s pre-reduction `hi % y` panics in Go before `Div64` is reached
  when `y == 0`; the model checks `y = 0` first for the same reason.

### Slices (`GoInLean/Semantics/Slice.lean`, `GoInLean/Stdlib/SlicesArr.lean`, `GoInLean/Stdlib/Slices.lean`)

Two models exist, for two purposes.

| Model | Representation | Used for | Spec clauses | Omissions |
|---|---|---|---|---|
| list model | `List α` | `Compact`, `Index`, `Contains`, `sort.Search` (kernel proofs) | element order and length only | capacity, aliasing, in-place mutation, `clear` |
| backing-array model | heap of arrays + descriptor `(arr, off, len, cap)`; operations in `StateT Heap (Except Panic)` | `Insert`, `Delete`, `Replace`, `Reverse`, `rotateLeft/Right`, `overlaps`, `startIdx` (bounded exhaustive search + Go replay) | "Slice types", "Slice expressions" (`s[i:j]`, `s[i:j:k]` bounds), "Appending to and copying slices" (in-place when `len+extra ≤ cap`, memmove `copy`), "Clear" | growth gives capacity exactly `len+extra` (Go rounds to a size class; the proofs/searches never depend on capacity values); zero value is `default`; `overlaps` is index-range intersection (Go compares addresses; element size 0 not modelled); indices are `Int` with negative → panic |

The backing-array model is validated by `go/tests/vectors_slices` +
`lake exe checkslices`: every configuration of one 5-element array (all
offsets/lengths/capacities of `s`, every aliasing or non-aliasing `v`, all
`i ≤ j`) is run through the real `slices.Insert/Delete/Replace` and through
the model, comparing both the returned contents and the whole backing array.
Go's own `TestInsertOverlap`/`TestReplaceOverlap` only use `s = a[:n]`
(offset 0, capacity `N`); the configurations here additionally vary the
offset and the capacity of `s`.

### Not modelled (initial boundary)

* `bytes` and `strings` (surveyed in Phase 3, not modelled); generic
  `slices.Sort` (pdqsort), `Concat`, `Grow`, `Clip`, `Repeat`.
* Strings, UTF-8, floating point, maps, pointers, interfaces, generics
  machinery, goroutines, channels, the memory model, `defer`/`recover`,
  `unsafe`.
* Compile-time constant arithmetic and constant overflow errors.
* Any architecture-dependent behaviour other than A1; any behaviour of Go
  versions other than go1.25.5.

## Behaviour classification

| Class | Examples in the modelled subset | Treatment |
|---|---|---|
| Specified by Go | wraparound, truncated division, shift semantics, conversions, panics on `/0` | modelled and validated |
| Implementation-defined | size of `int`/`uint`; out-of-range float→int | A1 fixes the size; floats excluded |
| Architecture-dependent | whether `math/bits` functions are intrinsics | A4: portable code modelled, binary tested |
| Version-dependent | `math/bits` API stable since Go 1.9/1.12; shift-count panics since 1.13 | pinned to go1.25.5 |
| Undefined by documentation | `Add64`/`Sub64` with carry/borrow ∉ {0,1} | precondition in the property; the unconstrained version is a recorded negative control (BITS-ADD-64-NOPRE) |
