import GoInLean.Semantics.Int
import GoInLean.Stdlib.BitsTables
import GoInLean.Semantics.BitSpec
/-!
# Model of Go `math/bits` (go1.25.5, `src/math/bits/bits.go`)

Each definition is a line-by-line transliteration of the pure-Go
implementation. The Go compiler intrinsifies many of these functions on
amd64/arm64, so the code modelled here is the *portable fallback* — this is
documented in `docs/semantic-boundary.md` (assumption A4). Comments give the
Go source line of go1.25.5 for traceability.

Conventions:
* **Operator precedence.** Go puts `* / % << >> & &^` on one level and
  `+ - | ^` on the next; Lean 4 gives `>>>`/`<<<` (75), `+` (65), `&&&` (60),
  `^^^` (58) and `|||` (55) distinct precedences. Every binary expression
  below is therefore fully parenthesised to match Go's parse tree. (The
  first draft was not, and the proofs in `GoInLean.Properties.Bits` caught
  the resulting model mismatch — see `docs/research-report.md`.)
* Go `int` results are `Go.int = BitVec 64`.
* Lookup-table indexing `tab[x]` is `tab x` below. In Go the index is a
  value of some unsigned type that is provably `< 256` at every call site
  (otherwise Go would panic); `Go.tab` returns `0` outside the table, and the
  properties file proves the index is in range wherever it matters.
* Width-generic helpers (`mulhiGeneric`, `divGeneric`) are used for `Mul64`
  / `Div64`, so that the *same* algorithm can be checked exhaustively at small
  widths. The 64-bit Go functions are definitional instances of the helpers.
-/
namespace Go.Bits
open Go


-- --- Len --- (bits.go:302-351)
def Len8 (x : uint8) : int := (tab len8tab x).zeroExtend 64
def Len16 (x : uint16) : int :=
  let n : int := if x ≥ (1 : uint16) <<< 8 then 8 else 0
  let x := if x ≥ (1 : uint16) <<< 8 then x >>> 8 else x
  n + (tab len8tab x).zeroExtend 64
def Len32 (x : uint32) : int :=
  let n : int := if x ≥ (1 : uint32) <<< 16 then 16 else 0
  let x := if x ≥ (1 : uint32) <<< 16 then x >>> 16 else x
  let n := if x ≥ (1 : uint32) <<< 8 then n + 8 else n
  let x := if x ≥ (1 : uint32) <<< 8 then x >>> 8 else x
  n + (tab len8tab x).zeroExtend 64
def Len64 (x : uint64) : int :=
  let n : int := if x ≥ (1 : uint64) <<< 32 then 32 else 0
  let x := if x ≥ (1 : uint64) <<< 32 then x >>> 32 else x
  let n := if x ≥ (1 : uint64) <<< 16 then n + 16 else n
  let x := if x ≥ (1 : uint64) <<< 16 then x >>> 16 else x
  let n := if x ≥ (1 : uint64) <<< 8 then n + 8 else n
  let x := if x ≥ (1 : uint64) <<< 8 then x >>> 8 else x
  n + (tab len8tab x).zeroExtend 64
def Len (x : uint) : int := Len64 x

-- --- LeadingZeros --- (bits.go:25-37)
def LeadingZeros8  (x : uint8)  : int := 8  - Len8 x
def LeadingZeros16 (x : uint16) : int := 16 - Len16 x
def LeadingZeros32 (x : uint32) : int := 32 - Len32 x
def LeadingZeros64 (x : uint64) : int := 64 - Len64 x
def LeadingZeros   (x : uint)   : int := 64 - Len x

-- --- TrailingZeros --- (bits.go:42-111)
def deBruijn32 : uint32 := 0x077CB531
def deBruijn64 : uint64 := 0x03f79d71b4ca8b09

def TrailingZeros8 (x : uint8) : int := (tab ntz8tab x).zeroExtend 64
def TrailingZeros16 (x : uint16) : int :=
  if x = 0 then 16 else
  (tab deBruijn32tab (((Go.convU 32 (x &&& -x)) * deBruijn32) >>> (32 - 5))).zeroExtend 64
def TrailingZeros32 (x : uint32) : int :=
  if x = 0 then 32 else
  (tab deBruijn32tab (((x &&& -x) * deBruijn32) >>> (32 - 5))).zeroExtend 64
def TrailingZeros64 (x : uint64) : int :=
  if x = 0 then 64 else
  (tab deBruijn64tab (((x &&& -x) * deBruijn64) >>> (64 - 6))).zeroExtend 64
def TrailingZeros (x : uint) : int := TrailingZeros64 x

-- --- OnesCount --- (bits.go:110-160)
def m0 : uint64 := 0x5555555555555555
def m1 : uint64 := 0x3333333333333333
def m2 : uint64 := 0x0f0f0f0f0f0f0f0f
def m3 : uint64 := 0x00ff00ff00ff00ff
def m4 : uint64 := 0x0000ffff0000ffff

def OnesCount8 (x : uint8) : int := (tab pop8tab x).zeroExtend 64
def OnesCount16 (x : uint16) : int :=
  (tab pop8tab (x >>> 8) + tab pop8tab (x &&& 0xff)).zeroExtend 64
def OnesCount32 (x : uint32) : int :=
  (tab pop8tab (x >>> 24) + tab pop8tab ((x >>> 16) &&& 0xff) +
   tab pop8tab ((x >>> 8) &&& 0xff) + tab pop8tab (x &&& 0xff)).zeroExtend 64
def OnesCount64 (x : uint64) : int :=
  let m : uint64 := ((1 : uint64) <<< 64) - 1   -- in Go this is the untyped constant 1<<64-1
  let x := ((x >>> 1) &&& (m0 &&& m)) + (x &&& (m0 &&& m))
  let x := ((x >>> 2) &&& (m1 &&& m)) + (x &&& (m1 &&& m))
  let x := ((x >>> 4) + x) &&& (m2 &&& m)
  let x := x + (x >>> 8)
  let x := x + (x >>> 16)
  let x := x + (x >>> 32)
  x &&& (((1 : uint64) <<< 7) - 1)
def OnesCount (x : uint) : int := OnesCount64 x

-- --- RotateLeft --- (bits.go:171-222). `k` is a Go `int`; `uint(k) & (n-1)`.
def RotateLeft8 (x : uint8) (k : int) : uint8 :=
  let s : uint := k &&& (8 - 1)
  (x <<< s) ||| (x >>> (8 - s))
def RotateLeft16 (x : uint16) (k : int) : uint16 :=
  let s : uint := k &&& (16 - 1)
  (x <<< s) ||| (x >>> (16 - s))
def RotateLeft32 (x : uint32) (k : int) : uint32 :=
  let s : uint := k &&& (32 - 1)
  (x <<< s) ||| (x >>> (32 - s))
def RotateLeft64 (x : uint64) (k : int) : uint64 :=
  let s : uint := k &&& (64 - 1)
  (x <<< s) ||| (x >>> (64 - s))
def RotateLeft (x : uint) (k : int) : uint := RotateLeft64 x k

-- --- ReverseBytes --- (bits.go:266-298)
def ReverseBytes16 (x : uint16) : uint16 := (x >>> 8) ||| (x <<< 8)
def ReverseBytes32 (x : uint32) : uint32 :=
  let m : uint32 := ((1 : uint32) <<< 32) - 1
  let x := ((x >>> 8) &&& (Go.convU 32 m3 &&& m)) ||| ((x &&& (Go.convU 32 m3 &&& m)) <<< 8)
  (x >>> 16) ||| (x <<< 16)
def ReverseBytes64 (x : uint64) : uint64 :=
  let m : uint64 := ((1 : uint64) <<< 64) - 1
  let x := ((x >>> 8) &&& (m3 &&& m)) ||| ((x &&& (m3 &&& m)) <<< 8)
  let x := ((x >>> 16) &&& (m4 &&& m)) ||| ((x &&& (m4 &&& m)) <<< 16)
  (x >>> 32) ||| (x <<< 32)
def ReverseBytes (x : uint) : uint := ReverseBytes64 x

-- --- Reverse --- (bits.go:226-262)
def Reverse8 (x : uint8) : uint8 := tab rev8tab x
def Reverse16 (x : uint16) : uint16 :=
  (tab rev8tab (x >>> 8)).zeroExtend 16 ||| ((tab rev8tab (x &&& 0xff)).zeroExtend 16 <<< 8)
def Reverse32 (x : uint32) : uint32 :=
  let m : uint32 := ((1 : uint32) <<< 32) - 1
  let x := ((x >>> 1) &&& (Go.convU 32 m0 &&& m)) ||| ((x &&& (Go.convU 32 m0 &&& m)) <<< 1)
  let x := ((x >>> 2) &&& (Go.convU 32 m1 &&& m)) ||| ((x &&& (Go.convU 32 m1 &&& m)) <<< 2)
  let x := ((x >>> 4) &&& (Go.convU 32 m2 &&& m)) ||| ((x &&& (Go.convU 32 m2 &&& m)) <<< 4)
  ReverseBytes32 x
def Reverse64 (x : uint64) : uint64 :=
  let m : uint64 := ((1 : uint64) <<< 64) - 1
  let x := ((x >>> 1) &&& (m0 &&& m)) ||| ((x &&& (m0 &&& m)) <<< 1)
  let x := ((x >>> 2) &&& (m1 &&& m)) ||| ((x &&& (m1 &&& m)) <<< 2)
  let x := ((x >>> 4) &&& (m2 &&& m)) ||| ((x &&& (m2 &&& m)) <<< 4)
  ReverseBytes64 x
def Reverse (x : uint) : uint := Reverse64 x

-- --- Add with carry --- (bits.go:355-394)
def Add32 (x y carry : uint32) : uint32 × uint32 :=
  let sum64 : uint64 := Go.convU 64 x + Go.convU 64 y + Go.convU 64 carry
  (Go.convU 32 sum64, Go.convU 32 (sum64 >>> 32))
def Add64 (x y carry : uint64) : uint64 × uint64 :=
  let sum := x + y + carry
  let carryOut := ((x &&& y) ||| Go.andNot (x ||| y) sum) >>> 63
  (sum, carryOut)
def Add (x y carry : uint) : uint × uint := Add64 x y carry

-- --- Subtract with borrow --- (bits.go:396-440)
def Sub32 (x y borrow : uint32) : uint32 × uint32 :=
  let diff := x - y - borrow
  let borrowOut := ((~~~x &&& y) ||| (~~~(x ^^^ y) &&& diff)) >>> 31
  (diff, borrowOut)
def Sub64 (x y borrow : uint64) : uint64 × uint64 :=
  let diff := x - y - borrow
  let borrowOut := ((~~~x &&& y) ||| (~~~(x ^^^ y) &&& diff)) >>> 63
  (diff, borrowOut)
def Sub (x y borrow : uint) : uint × uint := Sub64 x y borrow

-- --- Full-width multiply --- (bits.go:442-488)
def Mul32 (x y : uint32) : uint32 × uint32 :=
  let tmp : uint64 := Go.convU 64 x * Go.convU 64 y
  (Go.convU 32 (tmp >>> 32), Go.convU 32 tmp)

/-- The high half of `Mul64`, written for an arbitrary half-width `h`
(Go: `h = 32`, `mask32 = 1<<32 - 1`). -/
def mulhiGeneric (h : Nat) (x y : BitVec (2*h)) : BitVec (2*h) :=
  let mask : BitVec (2*h) := ((1 : BitVec (2*h)) <<< h) - 1
  let x0 := x &&& mask
  let x1 := x >>> h
  let y0 := y &&& mask
  let y1 := y >>> h
  let w0 := x0 * y0
  let t := (x1 * y0) + (w0 >>> h)
  let w1 := t &&& mask
  let w2 := t >>> h
  let w1 := w1 + x0 * y1
  (x1 * y1) + w2 + (w1 >>> h)
def Mul64 (x y : uint64) : uint64 × uint64 := (mulhiGeneric 32 x y, x * y)
def Mul (x y : uint) : uint × uint := Mul64 x y

-- --- Full-width divide --- (bits.go:490-570)
def Div32 (hi lo y : uint32) : Except Panic (uint32 × uint32) :=
  if y ≠ 0 ∧ y ≤ hi then .error .overflowError else
  let z : uint64 := (Go.convU 64 hi <<< 32) ||| Go.convU 64 lo
  -- `z/uint64(y)` panics in Go when y == 0 (uint64 division by zero)
  if y = 0 then .error .divideError else
  .ok (Go.convU 32 (z / Go.convU 64 y), Go.convU 32 (z % Go.convU 64 y))

/-- The correction loop of `Div64`,
`for q >= two32 || q*yn0 > two32*rhat+un { q--; rhat += yn1; if rhat >= two32 { break } }`,
written with explicit fuel (Go's loop needs at most two iterations; the
properties file checks fuel-independence at the widths it verifies). Only `q`
is live after the loop in Go, so only `q` is returned. -/
def divCorrect (h : Nat) (two yn1 yn0 un : BitVec (2*h)) :
    Nat → BitVec (2*h) → BitVec (2*h) → BitVec (2*h)
  | 0, q, _ => q
  | fuel+1, q, rhat =>
    if q ≥ two ∨ (q * yn0) > ((two * rhat) + un) then
      let q := q - 1
      let rhat := rhat + yn1
      if rhat ≥ two then q else divCorrect h two yn1 yn0 un fuel q rhat
    else q

/-- `Div64` for an arbitrary half-width `h` (Go: `h = 32`, so `2*h = 64`).
Returns `(quo, rem)`. The shift count `s` is a `uint` of the machine width `2*h` as in Go, and
`LeadingZeros64(y)` is replaced by the oracle `BitSpec.clzW y`, which
`Properties.Bits.LeadingZeros64_eq_clzW` proves equal to the Go function. -/
def divGeneric (h : Nat) (hi lo y : BitVec (2*h)) : Except Panic (BitVec (2*h) × BitVec (2*h)) :=
  if y = 0 then .error .divideError else
  if y ≤ hi then .error .overflowError else
  if hi = 0 then .ok (lo / y, lo % y) else
  let s : BitVec (2*h) := BitSpec.clzW y   -- Go: `s := uint(LeadingZeros64(y))`; see `LeadingZeros64_eq_clzW`
  let y := y <<< s
  let two : BitVec (2*h) := (1 : BitVec (2*h)) <<< h
  let mask : BitVec (2*h) := two - 1
  let yn1 := y >>> h
  let yn0 := y &&& mask
  let un32 := (hi <<< s) ||| (lo >>> (BitVec.ofNat (2*h) (2*h) - s))
  let un10 := lo <<< s
  let un1 := un10 >>> h
  let un0 := un10 &&& mask
  let q1 := un32 / yn1
  let rhat := un32 - (q1 * yn1)
  let q1 := divCorrect h two yn1 yn0 un1 8 q1 rhat
  let un21 := ((un32 * two) + un1) - (q1 * y)
  let q0 := un21 / yn1
  let rhat := un21 - (q0 * yn1)
  let q0 := divCorrect h two yn1 yn0 un0 8 q0 rhat
  .ok ((q1 * two) + q0, (((un21 * two) + un0) - (q0 * y)) >>> s)

def Div64 (hi lo y : uint64) : Except Panic (uint64 × uint64) := divGeneric 32 hi lo y
def Div (hi lo y : uint) : Except Panic (uint × uint) := Div64 hi lo y

def Rem32 (hi lo y : uint32) : Except Panic uint32 :=
  if y = 0 then .error .divideError else
  .ok (Go.convU 32 (((Go.convU 64 hi <<< 32) ||| Go.convU 64 lo) % Go.convU 64 y))
def remGeneric (h : Nat) (hi lo y : BitVec (2*h)) : Except Panic (BitVec (2*h)) :=
  if y = 0 then .error .divideError else   -- `hi%y` panics first in Go
  (divGeneric h (hi % y) lo y).map (·.2)
def Rem64 (hi lo y : uint64) : Except Panic uint64 := remGeneric 32 hi lo y
def Rem (hi lo y : uint) : Except Panic uint := Rem64 hi lo y

end Go.Bits
