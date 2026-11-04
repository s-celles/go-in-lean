import GoInLean.Semantics.Int

/-!
# IEEE 754 binary32 semantics over exact integer arithmetic

The binary32 mirror of `GoInLean.Semantics.Float64` for the SIMD oracle
(milestone J3): decode to an exact `(-1)^s * m * 2^e`, compute in Nat/Int
with no intermediate rounding, encode back with a single
round-to-nearest-even. Exponent field 8 bits (bias 127), mantissa field
23 bits, subnormal granularity 2^-149. NaN, infinities, signed zeros and
subnormals follow IEEE 754 and the Go spec; every NaN is one value and
comparisons treat NaN as unordered. The fused multiply-add carries the
single-rounding semantics that `MulAdd` documents (golang/go#80355 is
the emulated unfused divergence).
-/
namespace Go.Float32

structure Exact where
  sign : Bool
  mant : Nat
  exp : Int

inductive Val where
  | nan
  | inf (sign : Bool)
  | exact (e : Exact)

def nanBits : BitVec 32 := 0x7FC00001
def infBits (s : Bool) : BitVec 32 :=
  if s then 0xFF800000 else 0x7F800000
def zeroBits (s : Bool) : BitVec 32 :=
  if s then 0x80000000 else 0

def expField (x : BitVec 32) : Nat := (x >>> 23).toNat &&& 0xFF
def mantField (x : BitVec 32) : Nat := (x &&& 0x7FFFFF).toNat

def decode (x : BitVec 32) : Val :=
  let s := x.msb
  let ef := expField x
  let mf := mantField x
  if ef == 0xFF then
    if mf == 0 then .inf s else .nan
  else if ef == 0 then
    if mf == 0 then .exact ⟨s, 0, 0⟩ else .exact ⟨s, mf, -149⟩
  else .exact ⟨s, 2 ^ 23 + mf, ef - 150⟩

def assemble (sign : Bool) (ef : Nat) (mf : Nat) : BitVec 32 :=
  (if sign then (0x80000000 : BitVec 32) else 0)
    ||| ((BitVec.ofNat 32 ef) <<< 23)
    ||| (BitVec.ofNat 32 mf)

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
def encode (sign : Bool) (mant : Nat) (exp : Int) : BitVec 32 :=
  if mant == 0 then zeroBits sign
  else
    -- the exponent the value would have as a normal number
    let te := mant.log2 + exp
    if te > 127 then infBits sign
    else if te >= -126 then
      -- normal number: granularity 2^(te-23)
      let shift := te - 23 - exp
      let q := if shift <= 0 then mant <<< (Int.toNat (-shift)) else shiftRound mant (Int.toNat shift)
      if q >= 2 ^ 24 then
        -- rounded up into the next binade
        assemble sign (Int.toNat (te + 1 + 127)) 0
      else
        assemble sign (Int.toNat (te + 127)) (q - 2 ^ 23)
    else
      -- subnormal or zero: granularity 2^(-149), exponent fixed
      let d := exp + 149
      let q := if d >= 0 then mant <<< (Int.toNat d) else shiftRound mant (Int.toNat (-d))
      if q >= 2 ^ 23 then
        -- rounded into the normal range
        assemble sign 1 (q - 2 ^ 23)
      else
        assemble sign 0 q

def ofExact (e : Exact) : BitVec 32 := encode e.sign e.mant e.exp

/-- The exact sum of two finite values, as a signed integer at a common scale. -/
def exactSum (a b : Exact) : Int × Int :=
  let e := min a.exp b.exp
  let ma := Int.ofNat a.mant * (2 : Int) ^ Int.toNat (a.exp - e)
  let mb := Int.ofNat b.mant * (2 : Int) ^ Int.toNat (b.exp - e)
  let sa := if a.sign then -ma else ma
  let sb := if b.sign then -mb else mb
  (sa + sb, e)

def addBits (x y : BitVec 32) : BitVec 32 :=
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

def subBits (x y : BitVec 32) : BitVec 32 :=
  addBits x (y ^^^ 0x80000000)

def mulBits (x y : BitVec 32) : BitVec 32 :=
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
def fmaBits (x y z : BitVec 32) : BitVec 32 :=
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

def ltBits (x y : BitVec 32) : Bool :=
  match decode x, decode y with
  | .nan, _ => false
  | _, .nan => false
  | .inf true, .inf true => false
  | .inf true, .inf false => true
  | .inf true, .exact _ => true
  | .inf false, _ => false
  | .exact _, .inf true => false
  | .exact _, .inf false => true
  | .exact a, .exact b => finiteLt a b

def eqBits (x y : BitVec 32) : Bool :=
  match decode x, decode y with
  | .nan, _ => false
  | _, .nan => false
  | .exact a, .exact b =>
      (a.mant == 0 && b.mant == 0) || (a.sign == b.sign && a.mant == b.mant && a.exp == b.exp)
  | .inf s1, .inf s2 => s1 == s2
  | .inf _, .exact _ => false
  | .exact _, .inf _ => false

def leBits (x y : BitVec 32) : Bool := ltBits x y || eqBits x y

def isNaN (x : BitVec 32) : Bool :=
  expField x == 0xFF && mantField x != 0

/-- The Go builtin min: NaN if either is NaN; -0 wins over +0. -/
def minBits (x y : BitVec 32) : BitVec 32 :=
  if isNaN x || isNaN y then nanBits
  else if eqBits x y then (if x.msb then x else y)
  else if ltBits x y then x else y

/-- The Go builtin max: NaN if either is NaN; +0 wins over -0. -/
def maxBits (x y : BitVec 32) : BitVec 32 :=
  if isNaN x || isNaN y then nanBits
  else if eqBits x y then (if !x.msb then x else y)
  else if ltBits y x then x else y

end Go.Float32
