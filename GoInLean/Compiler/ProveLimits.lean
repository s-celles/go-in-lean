import Std.Tactic.BVDecide
import GoInLean.Semantics.BitSpec
/-!
# Soundness of the interval ("limit") arithmetic of the `prove` pass (Go master `babb75be`)

Transliteration of `ssa/prove.go` (`Limit.Add/Sub/Com/Neg/Mul/Exp2/Bitlen/Ctz/Popcount`,
`PropagateUnsignedSignedRelationship`) and of three `flowLimit` cases in
`ssacompile/prove.go` (Or, Xor, Trunc). A concrete `w`-bit value `v` is *in* a limit when
`Min ≤ₛ sext v ≤ₛ Max` and `Umin ≤ zext v ≤ Umax` (64-bit). Theorems: if the operands are in
their limits, the result of the Go operation is in the computed limit.

Hypothesis `norm w l`: the limit lies inside the range of a `w`-bit type. `newLimit`
maintains it for every value (it intersects with `InitLimit`'s `NoLimitForBitsize`), EXCEPT
that `InitLimit` gives a `Const64` its exact 64-bit value whatever its type: a `Const64` typed
narrower than 64 bits (golang/go#81868, golang/go#82767) yields a non-normalised limit.
`com32_needs_norm` shows the hypothesis is necessary.
-/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace Go.Compiler.ProveLimits

abbrev I := BitVec 64

structure Lim where
  mn : I
  mx : I
  umn : I
  umx : I

def inL (w : Nat) (l : Lim) (v : BitVec w) : Prop :=
  l.mn.sle (v.signExtend 64) ∧ (v.signExtend 64).sle l.mx ∧ l.umn ≤ v.setWidth 64 ∧ v.setWidth 64 ≤ l.umx
def norm (w : Nat) (l : Lim) : Prop :=
  l.mn = (l.mn.setWidth w).signExtend 64 ∧ l.mx = (l.mx.setWidth w).signExtend 64 ∧
  l.umn = (l.umn.setWidth w).setWidth 64 ∧ l.umx = (l.umx.setWidth w).setWidth 64

def smax (a b : I) : I := if a.slt b then b else a
def smin (a b : I) : I := if a.slt b then a else b
def umax (a b : I) : I := if a < b then b else a
def umin (a b : I) : I := if a < b then a else b

def noLimitBits (w : Nat) : Lim :=
  ⟨-((1 : I) <<< (w - 1)), ((1 : I) <<< (w - 1)) - 1, 0, ((1 : I) <<< w) - 1⟩
def noLimit : Lim := ⟨0x8000000000000000, 0x7FFFFFFFFFFFFFFF, 0, 0xFFFFFFFFFFFFFFFF⟩

/-- `fitsInBits(x, b)` (signed). -/
def fitsS (w : Nat) (x : I) : Bool :=
  if w = 64 then true else
  let m : I := (-1 : I) <<< (w - 1)
  m.sle x && x.sle (-m - 1)
/-- `FitsInBitsU(x, b)`: `x>>b == 0`. -/
def fitsU (w : Nat) (x : I) : Bool := x >>> w == 0
/-- `SafeAdd` / `safeAddU` / `SafeSub` / `SafeSubU` ok-flags and sums. -/
def addOk (w : Nat) (x y : I) : Bool :=
  let s := x + y
  !((!x.msb && !y.msb && s.msb) || (x.msb && y.msb && !s.msb)) && fitsS w s
def addUOk (w : Nat) (x y : I) : Bool := let s := x + y; !(s < x || s < y) && fitsU w s
def subOk (w : Nat) (x y : I) : Bool :=
  if y = 0x8000000000000000 then (x != 0x7FFFFFFFFFFFFFFF) && addOk w (x + 1) (-(y + 1))
  else addOk w x (-y)
def subVal (x y : I) : I := if y = 0x8000000000000000 then (x + 1) + (-(y + 1)) else x + (-y)
def subUOk (w : Nat) (x y : I) : Bool := !(x < y) && fitsU w (x - y)

/-- `ConvertIntWithBitsize[uint64](x, b)` and `[int64]`. -/
def cvtU (w : Nat) (x : I) : I := (x.setWidth w).setWidth 64
def cvtS (w : Nat) (x : I) : I := (x.setWidth w).signExtend 64

/-- `Limit.Add` -/
def add (w : Nat) (l l2 : Lim) : Lim :=
  let isL := l.mn == l.mx || l.umn == l.umx
  let lc := if l.mn == l.mx then cvtU w l.mn else l.umn
  let isL2 := l2.mn == l2.mx || l2.umn == l2.umx
  let l2c := if l2.mn == l2.mx then cvtU w l2.mn else l2.umn
  let r := (lc + l2c) &&& (((1 : I) <<< w) - 1)
  let sOk := addOk w l.mn l2.mn && addOk w l.mx l2.mx
  let uOk := addUOk w l.umn l2.umn && addUOk w l.umx l2.umx
  let c := isL && isL2
  ⟨if c then cvtS w r else if sOk then l.mn + l2.mn else noLimit.mn,
   if c then cvtS w r else if sOk then l.mx + l2.mx else noLimit.mx,
   if c then r else if uOk then l.umn + l2.umn else noLimit.umn,
   if c then r else if uOk then l.umx + l2.umx else noLimit.umx⟩

/-- `Limit.Sub` -/
def sub (w : Nat) (l l2 : Lim) : Lim :=
  let sOk := subOk w l.mn l2.mx && subOk w l.mx l2.mn
  let uOk := subUOk w l.umn l2.umx && subUOk w l.umx l2.umn
  ⟨if sOk then subVal l.mn l2.mx else noLimit.mn, if sOk then subVal l.mx l2.mn else noLimit.mx,
   if uOk then l.umn - l2.umx else noLimit.umn, if uOk then l.umx - l2.umn else noLimit.umx⟩

/-- `Limit.Com` -/
def com (w : Nat) (l : Lim) : Lim :=
  -- for w = 64 the Go code uses ^x directly; (~~~(x.setWidth 64)).signExtend 64 = ~~~x, so one formula covers it
  ⟨(~~~(l.mx.setWidth w)).signExtend 64, (~~~(l.mn.setWidth w)).signExtend 64,
   (~~~(l.umx.setWidth w)).setWidth 64, (~~~(l.umn.setWidth w)).setWidth 64⟩

/-- `Limit.Neg = Com(b).Add(1, b)` -/
def neg (w : Nat) (l : Lim) : Lim := add w (com w l) ⟨1, 1, 1, 1⟩

/-- `Limit.Mul` (unsigned part only; signed part is `NoLimit`). -/
def mul (w : Nat) (l l2 : Lim) : Lim :=
  let p : BitVec 128 := l.umx.setWidth 128 * l2.umx.setWidth 128
  let ok := p.extractLsb' 64 64 == 0 && fitsU w (p.setWidth 64)
  ⟨noLimit.mn, noLimit.mx, if ok then l.umn * l2.umn else noLimit.umn, if ok then p.setWidth 64 else noLimit.umx⟩

/-- `Limit.Exp2` -/
def exp2 (w : Nat) (l : Lim) : Lim :=
  let ok := l.umx < BitVec.ofNat 64 w
  ⟨noLimit.mn, noLimit.mx, if ok then (1 : I) <<< l.umn else 0, if ok then (1 : I) <<< l.umx else noLimit.umx⟩

/-- `PropagateUnsignedSignedRelationship` (soundness only needs the two refinements). -/
def signW (w : Nat) (x : I) : I := (x <<< (64 - w)).sshiftRight' (63 : I)
def propagate (w : Nat) (l : Lim) : Lim :=
  let c1 := signW w l.mn == signW w l.mx
  let umn1 := if c1 then umax l.umn (cvtU w l.mn) else l.umn
  let umx1 := if c1 then umin l.umx (cvtU w l.mx) else l.umx
  let sumin := cvtS w umn1
  let sumax := cvtS w umx1
  let c2 := signW w sumin == signW w sumax
  ⟨if c2 then smax l.mn sumin else l.mn, if c2 then smin l.mx sumax else l.mx, umn1, umx1⟩

/-- `Limit.Bitlen` -/
def bitlen (l : Lim) : Lim := ⟨noLimit.mn, noLimit.mx, BitSpec.len l.umn, BitSpec.len l.umx⟩

/-- `UnsignedFixedLeadingBits` -/
def varyingBits (l : Lim) : I := BitSpec.len (l.umn ^^^ l.umx)
def fixedBits (l : Lim) : I := l.umn &&& ~~~(((1 : I) <<< varyingBits l) - 1)

/-- `Limit.Ctz` -/
def ctz (w : Nat) (l : Lim) : Lim :=
  let fixed := fixedBits l
  let varying := varyingBits l
  let tzf := BitSpec.ctz fixed
  let capped := if tzf < BitVec.ofNat 64 w then tzf else BitVec.ofNat 64 w
  let c0 := varying == 0
  let c1 := l.umn &&& (((1 : I) <<< varying) - 1) != 0
  ⟨if c0 then capped else noLimit.mn, if c0 then capped else noLimit.mx, if c0 then capped else 0,
   if c0 then capped else if c1 then umin noLimit.umx (varying - 1) else capped⟩

/-- `Limit.Popcount` -/
def popcount (l : Lim) : Lim :=
  let fixed := fixedBits l
  let varying := varyingBits l
  let mask := ((1 : I) <<< varying) - 1
  let mx0 := BitSpec.popcount fixed + varying
  let mn0 := BitSpec.popcount fixed
  let mx := if BitSpec.popcount (l.umx &&& mask) != varying then mx0 - 1 else mx0
  let mn := if l.umn &&& mask != 0 then mn0 + 1 else mn0
  ⟨noLimit.mn, noLimit.mx, mn, mx⟩

macro "lim_unfold" : tactic => `(tactic| simp only [inL, norm, add, sub, com, neg, mul, exp2, propagate,
  bitlen, ctz, popcount, varyingBits, fixedBits, signW, cvtU, cvtS, addOk, addUOk, subOk, subVal, subUOk,
  fitsS, fitsU, noLimit, smax, smin, umax, umin, BitSpec.len, BitSpec.ctz, BitSpec.popcount,
  List.range, List.range.loop, List.foldl, List.foldr] at *)

/-- Without normalisation, `Com(32)` is unsound (the non-normalised limit of a Const64 typed int32). -/
theorem com32_needs_norm (mn mx umn umx : I) (v : BitVec 32) (hv : v = 0xFFFFFFFF)
    (h1 : mn = 0xFFFFFFFFFFFFFFFF) (h2 : mx = 0xFFFFFFFFFFFFFFFF) (h3 : umn = 0xFFFFFFFF)
    (h4 : umx = 0xFFFFFFFF7FFFFFFF) :
    inL 32 ⟨mn, mx, umn, umx⟩ v ∧ ¬ inL 32 (com 32 ⟨mn, mx, umn, umx⟩) (~~~v) := by
  subst hv h1 h2 h3 h4; simp only [inL, com]; decide

theorem add_sound_8 (a b : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (l2 : Lim) (h2n : norm 8 l2) (ha : inL 8 l1 a) (hb : inL 8 l2 b) :
    inL 8 (add 8 l1 l2) (a + b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem sub_sound_8 (a b : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (l2 : Lim) (h2n : norm 8 l2) (ha : inL 8 l1 a) (hb : inL 8 l2 b) :
    inL 8 (sub 8 l1 l2) (a - b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem com_sound_8 (a : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (ha : inL 8 l1 a) : inL 8 (com 8 l1) (~~~a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem neg_sound_8 (a : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (ha : inL 8 l1 a) : inL 8 (neg 8 l1) (-a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem propagate_sound_8 (a : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (ha : inL 8 l1 a) : inL 8 (propagate 8 l1) a := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem bitlen_sound_8 (a : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (ha : inL 8 l1 a) :
    (bitlen l1).umn ≤ BitSpec.len a ∧ BitSpec.len a ≤ (bitlen l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem ctz_sound_8 (a : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (ha : inL 8 l1 a) :
    (ctz 8 l1).umn ≤ BitSpec.ctz a ∧ BitSpec.ctz a ≤ (ctz 8 l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem popcount_sound_8 (a : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (ha : inL 8 l1 a) :
    (popcount l1).umn ≤ BitSpec.popcount a ∧ BitSpec.popcount a ≤ (popcount l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem mul_sound_8 (a b : BitVec 8) (l1 : Lim) (h1n : norm 8 l1) (l2 : Lim) (h2n : norm 8 l2) (ha : inL 8 l1 a) (hb : inL 8 l2 b) :
    (mul 8 l1 l2).umn ≤ (a * b).setWidth 64 ∧ (a * b).setWidth 64 ≤ (mul 8 l1 l2).umx := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem add_sound_16 (a b : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (l2 : Lim) (h2n : norm 16 l2) (ha : inL 16 l1 a) (hb : inL 16 l2 b) :
    inL 16 (add 16 l1 l2) (a + b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem sub_sound_16 (a b : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (l2 : Lim) (h2n : norm 16 l2) (ha : inL 16 l1 a) (hb : inL 16 l2 b) :
    inL 16 (sub 16 l1 l2) (a - b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem com_sound_16 (a : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (ha : inL 16 l1 a) : inL 16 (com 16 l1) (~~~a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem neg_sound_16 (a : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (ha : inL 16 l1 a) : inL 16 (neg 16 l1) (-a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem propagate_sound_16 (a : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (ha : inL 16 l1 a) : inL 16 (propagate 16 l1) a := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem bitlen_sound_16 (a : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (ha : inL 16 l1 a) :
    (bitlen l1).umn ≤ BitSpec.len a ∧ BitSpec.len a ≤ (bitlen l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem ctz_sound_16 (a : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (ha : inL 16 l1 a) :
    (ctz 16 l1).umn ≤ BitSpec.ctz a ∧ BitSpec.ctz a ≤ (ctz 16 l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem popcount_sound_16 (a : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (ha : inL 16 l1 a) :
    (popcount l1).umn ≤ BitSpec.popcount a ∧ BitSpec.popcount a ≤ (popcount l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem mul_sound_16 (a b : BitVec 16) (l1 : Lim) (h1n : norm 16 l1) (l2 : Lim) (h2n : norm 16 l2) (ha : inL 16 l1 a) (hb : inL 16 l2 b) :
    (mul 16 l1 l2).umn ≤ (a * b).setWidth 64 ∧ (a * b).setWidth 64 ≤ (mul 16 l1 l2).umx := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem add_sound_32 (a b : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (l2 : Lim) (h2n : norm 32 l2) (ha : inL 32 l1 a) (hb : inL 32 l2 b) :
    inL 32 (add 32 l1 l2) (a + b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem sub_sound_32 (a b : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (l2 : Lim) (h2n : norm 32 l2) (ha : inL 32 l1 a) (hb : inL 32 l2 b) :
    inL 32 (sub 32 l1 l2) (a - b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem com_sound_32 (a : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (ha : inL 32 l1 a) : inL 32 (com 32 l1) (~~~a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem neg_sound_32 (a : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (ha : inL 32 l1 a) : inL 32 (neg 32 l1) (-a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem propagate_sound_32 (a : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (ha : inL 32 l1 a) : inL 32 (propagate 32 l1) a := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem bitlen_sound_32 (a : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (ha : inL 32 l1 a) :
    (bitlen l1).umn ≤ BitSpec.len a ∧ BitSpec.len a ≤ (bitlen l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem ctz_sound_32 (a : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (ha : inL 32 l1 a) :
    (ctz 32 l1).umn ≤ BitSpec.ctz a ∧ BitSpec.ctz a ≤ (ctz 32 l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem popcount_sound_32 (a : BitVec 32) (l1 : Lim) (h1n : norm 32 l1) (ha : inL 32 l1 a) :
    (popcount l1).umn ≤ BitSpec.popcount a ∧ BitSpec.popcount a ≤ (popcount l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem add_sound_64 (a b : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (l2 : Lim) (h2n : norm 64 l2) (ha : inL 64 l1 a) (hb : inL 64 l2 b) :
    inL 64 (add 64 l1 l2) (a + b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem sub_sound_64 (a b : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (l2 : Lim) (h2n : norm 64 l2) (ha : inL 64 l1 a) (hb : inL 64 l2 b) :
    inL 64 (sub 64 l1 l2) (a - b) := by
  obtain ⟨_, _, _, _⟩ := l1; obtain ⟨_, _, _, _⟩ := l2; lim_unfold; bv_decide (config := {timeout := 300})
theorem com_sound_64 (a : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (ha : inL 64 l1 a) : inL 64 (com 64 l1) (~~~a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem neg_sound_64 (a : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (ha : inL 64 l1 a) : inL 64 (neg 64 l1) (-a) := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem propagate_sound_64 (a : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (ha : inL 64 l1 a) : inL 64 (propagate 64 l1) a := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem bitlen_sound_64 (a : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (ha : inL 64 l1 a) :
    (bitlen l1).umn ≤ BitSpec.len a ∧ BitSpec.len a ≤ (bitlen l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem ctz_sound_64 (a : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (ha : inL 64 l1 a) :
    (ctz 64 l1).umn ≤ BitSpec.ctz a ∧ BitSpec.ctz a ≤ (ctz 64 l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
theorem popcount_sound_64 (a : BitVec 64) (l1 : Lim) (h1n : norm 64 l1) (ha : inL 64 l1 a) :
    (popcount l1).umn ≤ BitSpec.popcount a ∧ BitSpec.popcount a ≤ (popcount l1).umx := by
  obtain ⟨_, _, _, _⟩ := l1; lim_unfold; bv_decide (config := {timeout := 300})
end Go.Compiler.ProveLimits
