import GoInLean.Semantics.Int

/-!
# IEEE 754 binary64 semantics over exact integer arithmetic

An executable model of float64 for the SIMD oracle (milestone J3, step 2):
every operation decodes the operands to an exact value `(-1)^s * m * 2^e`
(`m : Nat`, `e : Int`), computes the result *exactly* in Nat/Int (bignum, no
intermediate rounding), and encodes back with a single round-to-nearest-even.
The fused multiply-add - the semantics the simd package documents for MulAdd
(golang/go#80355: the emulated path rounds the product first, which is the
divergence this model exists to see) - is exactly the case where the exact
product+sum would not fit a float and the single rounding matters.

NaN, infinities, signed zeros, subnormals follow IEEE 754 and the Go spec
(min/max propagate NaN, order -0 below +0); every NaN is one value here and
comparisons treat NaN as unordered.
-/
namespace Go.Float64

structure Exact where
  sign : Bool
  mant : Nat
  exp : Int

inductive Val where
  | nan
  | inf (sign : Bool)
  | exact (e : Exact)

def nanBits : BitVec 64 := 0x7FF8000000000001
def infBits (s : Bool) : BitVec 64 :=
  if s then 0xFFF0000000000000 else 0x7FF0000000000000
def zeroBits (s : Bool) : BitVec 64 :=
  if s then 0x8000000000000000 else 0

def expField (x : BitVec 64) : Nat := (x >>> 52).toNat &&& 0x7FF
def mantField (x : BitVec 64) : Nat := (x &&& 0xFFFFFFFFFFFFF).toNat

def decode (x : BitVec 64) : Val :=
  let s := x.msb
  let ef := expField x
  let mf := mantField x
  if ef == 0x7FF then
    if mf == 0 then .inf s else .nan
  else if ef == 0 then
    if mf == 0 then .exact ⟨s, 0, 0⟩ else .exact ⟨s, mf, -1074⟩
  else .exact ⟨s, 2 ^ 52 + mf, ef - 1075⟩

def assemble (sign : Bool) (ef : Nat) (mf : Nat) : BitVec 64 :=
  (if sign then (0x8000000000000000 : BitVec 64) else 0)
    ||| ((BitVec.ofNat 64 ef) <<< 52)
    ||| (BitVec.ofNat 64 mf)

/-- Round `m / 2^k` to nearest-even (k > 0), for the granularity alignment. -/
def shiftRound (m : Nat) (k : Nat) : Nat :=
  let q := m >>> k
  let r := m &&& ((1 <<< k) - 1)
  let half := 1 <<< (k - 1)
  if r > half then q + 1
  else if r == half then q + (q &&& 1)
  else q

/-- Encode `sign * mant * 2^exp` (mant > 0) with a single round-to-nearest-even;
the whole IEEE discipline of this module lives here. -/
def encode (sign : Bool) (mant : Nat) (exp : Int) : BitVec 64 :=
  if mant == 0 then zeroBits sign
  else
    -- the exponent the value would have as a normal number
    let te := mant.log2 + exp
    if te > 1023 then infBits sign
    else if te >= -1022 then
      -- normal number: granularity 2^(te-52)
      let shift := te - 52 - exp
      let q := if shift <= 0 then mant <<< (Int.toNat (-shift)) else shiftRound mant (Int.toNat shift)
      if q >= 2 ^ 53 then
        -- rounded up into the next binade
        assemble sign (Int.toNat (te + 1 + 1023)) 0
      else
        assemble sign (Int.toNat (te + 1023)) (q - 2 ^ 52)
    else
      -- subnormal or zero: granularity 2^(-1074), exponent fixed
      let d := exp + 1074
      let q := if d >= 0 then mant <<< (Int.toNat d) else shiftRound mant (Int.toNat (-d))
      if q >= 2 ^ 52 then
        -- rounded into the normal range
        assemble sign 1 (q - 2 ^ 52)
      else
        assemble sign 0 q

def ofExact (e : Exact) : BitVec 64 := encode e.sign e.mant e.exp

/-- The exact sum of two finite values, as a signed integer at a common scale. -/
def exactSum (a b : Exact) : Int × Int :=
  let e := min a.exp b.exp
  let ma := Int.ofNat a.mant * (2 : Int) ^ Int.toNat (a.exp - e)
  let mb := Int.ofNat b.mant * (2 : Int) ^ Int.toNat (b.exp - e)
  let sa := if a.sign then -ma else ma
  let sb := if b.sign then -mb else mb
  (sa + sb, e)

def addBits (x y : BitVec 64) : BitVec 64 :=
  match decode x, decode y with
  | .nan, _ => nanBits
  | _, .nan => nanBits
  | .inf s, .inf t => if s == t then infBits s else nanBits
  | .inf s, _ => infBits s
  | _, .inf t => infBits t
  | .exact a, .exact b =>
      if a.mant == 0 && b.mant == 0 then
        -- both zero: -0 only when both are -0
        zeroBits (a.sign && b.sign)
      else
        let (s, e) := exactSum a b
        if s == 0 then zeroBits false
        else if s > 0 then encode false s.toNat e
        else encode true (-s).toNat e

def subBits (x y : BitVec 64) : BitVec 64 :=
  addBits x (y ^^^ 0x8000000000000000)

def mulBits (x y : BitVec 64) : BitVec 64 :=
  match decode x, decode y with
  | .nan, _ => nanBits
  | _, .nan => nanBits
  | .exact a, .exact b =>
      if a.mant == 0 || b.mant == 0 then zeroBits (a.sign != b.sign)
      else encode (a.sign != b.sign) (a.mant * b.mant) (a.exp + b.exp)
  | .inf s, .inf t => infBits (s != t)
  | .inf s, .exact e => if e.mant == 0 then nanBits else infBits (s != e.sign)
  | .exact e, .inf t => if e.mant == 0 then nanBits else infBits (e.sign != t)

/-- The fused multiply-add: `x*y + z` with a single rounding - the spec of
`math.FMA` and of the simd package's MulAdd. -/
def fmaBits (x y z : BitVec 64) : BitVec 64 :=
  match decode x, decode y with
  | .nan, _ => nanBits
  | _, .nan => nanBits
  | .inf s, .inf t =>
      -- inf * inf: the product is inf with sign (s != t)
      let psign := (s != t)
      match decode z with
      | .nan => nanBits
      | .inf zs => if zs != psign then nanBits else infBits zs
      | .exact c => if c.mant == 0 && ((s != t) == c.sign) then nanBits else infBits psign
  | .inf s, .exact a =>
      if a.mant == 0 then nanBits
      else
        let psign := (s != a.sign)
        match decode z with
        | .nan => nanBits
        | .inf zs => if zs != psign then nanBits else infBits zs
        | _ => infBits psign
  | .exact a, .inf t =>
      if a.mant == 0 then nanBits
      else
        let psign := (a.sign != t)
        match decode z with
        | .nan => nanBits
        | .inf zs => if zs != psign then nanBits else infBits zs
        | _ => infBits psign
  | .exact a, .exact b =>
      if a.mant == 0 || b.mant == 0 then
        -- the product is a signed zero; the result is zero + z
        addBits (zeroBits (a.sign != b.sign)) z
      else
        match decode z with
        | .nan => nanBits
        | .inf zs => infBits zs
        | .exact c =>
            let pe := a.exp + b.exp
            let e := min pe c.exp
            let p := Int.ofNat (a.mant * b.mant) * (2 : Int) ^ Int.toNat (pe - e)
            let mc := Int.ofNat c.mant * (2 : Int) ^ Int.toNat (c.exp - e)
            let sp := if a.sign != b.sign then -p else p
            let sc := if c.sign then -mc else mc
            let s := sp + sc
            if s == 0 then zeroBits false
            else if s > 0 then encode false s.toNat e
            else encode true (-s).toNat e

/-- Comparison on finite values (both decoded, non-NaN): with equal signs the
magnitudes order by (exp, mant), lexicographically, positive order up,
negative order down. -/
def finiteLt (a b : Exact) : Bool :=
  if a.sign != b.sign then a.sign
  else if a.mant == 0 && b.mant == 0 then false
  else if a.mant == 0 then !b.sign
  else if b.mant == 0 then a.sign
  else if a.sign then
    a.exp > b.exp || (a.exp == b.exp && a.mant > b.mant)
  else
    a.exp < b.exp || (a.exp == b.exp && a.mant < b.mant)

def ltBits (x y : BitVec 64) : Bool :=
  match decode x, decode y with
  | .exact a, .exact b => finiteLt a b
  | _, _ => false

def eqBits (x y : BitVec 64) : Bool :=
  match decode x, decode y with
  | .nan, _ => false
  | _, .nan => false
  | .exact a, .exact b =>
      (a.mant == 0 && b.mant == 0) || (a.sign == b.sign && a.mant == b.mant && a.exp == b.exp)
  | _, _ => true

def leBits (x y : BitVec 64) : Bool := ltBits x y || eqBits x y

def isNaN (x : BitVec 64) : Bool :=
  expField x == 0x7FF && mantField x != 0

/-- The Go builtin min: NaN if either is NaN; -0 wins over +0. -/
def minBits (x y : BitVec 64) : BitVec 64 :=
  if isNaN x || isNaN y then nanBits
  else if eqBits x y then (if x.msb then x else y)
  else if ltBits x y then x else y

/-- The Go builtin max: NaN if either is NaN; +0 wins over -0. -/
def maxBits (x y : BitVec 64) : BitVec 64 :=
  if isNaN x || isNaN y then nanBits
  else if eqBits x y then (if !x.msb then x else y)
  else if ltBits y x then x else y

end Go.Float64
