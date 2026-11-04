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

/-!
## Division and square root: single rounding at the final grid

The binary32 mirror of the float64 division and square root: the exact
quotient is scaled to integer units at the grid the result lands on
(normal `te - 23`, subnormal `-149`) and rounded nearest-even there once,
with the remainder as the sticky term.
-/

/-- The exact quotient `(ma/mb) * 2^(ea-eb)` of two positive finite
values, rounded once - the IEEE division. -/
def divPositive (sign : Bool) (ma ea mb eb : Int) : BitVec 32 :=
  let la : Int := (Int.toNat ma).log2 + 1
  let lb : Int := (Int.toNat mb).log2 + 1
  let s := ea - eb
  let lead : Int := if ma * (2 : Int) ^ Int.toNat lb >= mb * (2 : Int) ^ Int.toNat la
    then la - lb else la - lb - 1
  let te := lead + s
  if te > 127 then infBits sign
  else
    let g : Int := if te >= -126 then te - 23 else -149
    let K := s - g
    let N := if K >= 0 then ma * (2 : Int) ^ Int.toNat K else ma
    let D := if K >= 0 then mb else mb * (2 : Int) ^ Int.toNat (-K)
    let q := N / D
    let r := N % D
    let u : Int := if 2 * r > D then q + 1
      else if 2 * r == D then (if q % 2 == 1 then q + 1 else q)
      else q
    if te >= -126 then
      if u >= 2 ^ 24 then
        -- carried into the next binade (te+1 = 128 lands on the inf pattern)
        assemble sign (Int.toNat (te + 1 + 127)) 0
      else assemble sign (Int.toNat (te + 127)) (Int.toNat (u - 2 ^ 23))
    else
      if u >= 2 ^ 23 then assemble sign 1 (Int.toNat (u - 2 ^ 23))
      else assemble sign 0 (Int.toNat u)

/-- The IEEE division. -/
def divBits (x y : BitVec 32) : BitVec 32 :=
  match decode x, decode y with
  | .nan, _ => nanBits
  | _, .nan => nanBits
  | .inf _, .inf _ => nanBits
  | .inf s, .exact e => if e.mant == 0 then nanBits else infBits (s != e.sign)
  | .exact e, .inf t => zeroBits (e.sign != t)
  | .exact a, .exact b =>
      if b.mant == 0 then
        if a.mant == 0 then nanBits else infBits (a.sign != b.sign)
      else if a.mant == 0 then zeroBits (a.sign != b.sign)
      else divPositive (a.sign != b.sign) a.mant a.exp b.mant b.exp

/-- The IEEE square root. sqrt(-0) is -0; sqrt of a negative is NaN; the
result of a positive finite is always normal (>= 2^-75). -/
def sqrtBits (x : BitVec 32) : BitVec 32 :=
  match decode x with
  | .nan => nanBits
  | .inf s => if s then nanBits else infBits false
  | .exact e =>
      if e.mant == 0 then zeroBits e.sign
      else if e.sign then nanBits
      else
        let even := e.exp % 2 == 0
        let m := if even then e.mant else e.mant * 2
        let ex : Int := if even then e.exp else e.exp - 1
        let lm : Int := (Int.toNat m).log2
        let he : Int := lm + ex
        let te : Int := if he >= 0 then he / 2 else -(((Int.toNat (-he)) + 1) / 2)
        -- te >= -75 > -126: the normal grid always
        let g : Int := te - 23
        let A : Int := m * (2 : Int) ^ Int.toNat (ex - 2 * g)
        let s0 := (Nat.sqrt (Int.toNat A) : Int)
        let u : Int := if (2 * s0 + 1) ^ 2 < 4 * A then s0 + 1 else s0
        if u >= 2 ^ 24 then
          assemble false (Int.toNat (te + 1 + 127)) 0
        else assemble false (Int.toNat (te + 127)) (Int.toNat (u - 2 ^ 23))

end Go.Float32
