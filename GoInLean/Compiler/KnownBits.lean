import Std.Tactic.BVDecide
/-!
# Soundness of the new `knownbits` SSA pass (Go master `babb75be`, `ssa/known_bits.go`)

Abstract state of a value: `(value, known)` as int64, with the pass's invariants
(1) `value &&& known = value`, (2) both sign-extended from the value's width W.
A concrete W-bit value `a` is represented as `rep a = a.signExtend 64` and *fits* a state
when `rep a &&& known = value`. `norm W` is the pass's deferred normalisation (sign-extend from
the result width, then `value &= known`). Each theorem: if the inputs match their states, the
concrete result fits the state computed by the transliterated `fold` case.
-/
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
namespace Go.Compiler.KnownBits

abbrev I := BitVec 64

def rep {w : Nat} (a : BitVec w) : I := a.signExtend 64
def sx (w : Nat) (v : I) : I := (v.setWidth w).signExtend 64
def inv (w : Nat) (v k : I) : Prop := v &&& k = v ∧ v = sx w v ∧ k = sx w k
def fits (r v k : I) : Prop := r &&& k = v
/-- deferred block of `fold` for an integer result of width `w`. -/
def norm (w : Nat) (vk : I × I) : I × I := (sx w vk.1 &&& sx w vk.2, sx w vk.2)
/-- deferred block for a boolean result (size 1): `value &= 1; known |= ^1`, then sign-extend from 8. -/
def normB (vk : I × I) : I × I :=
  let v := vk.1 &&& 1; let k := vk.2 ||| ~~~1
  (sx 8 v &&& sx 8 k, sx 8 k)
def brep (b : Bool) : I := if b then 1 else 0

-- ---------------------------------------------------------------- fold cases (known_bits.go)
def andF (x xk y yk : I) : I × I := (x &&& y, (x &&& y) ||| (~~~x &&& xk) ||| (~~~y &&& yk))
def orF (x xk y yk : I) : I × I := (x ||| y, x ||| y ||| (~~~x &&& ~~~y &&& (xk &&& yk)))
def xorF (x xk y yk : I) : I × I := (x ^^^ y, xk &&& yk)
def comF (x xk : I) : I × I := (~~~x, xk)
/-- `OpEq*` case, written componentwise (same control flow as the Go code). -/
def eqF (x xk y yk : I) : I × I :=
  (if (x ^^^ y) &&& xk &&& yk != 0 then 0 else if xk == -1 && yk == -1 then brep (x == y) else 0,
   if (x ^^^ y) &&& xk &&& yk != 0 then -1 else if xk == -1 && yk == -1 then -1 else -1 <<< 1)
def neqF (x xk y yk : I) : I × I :=
  (if (x ^^^ y) &&& xk &&& yk != 0 then 1 else if xk == -1 && yk == -1 then brep (x != y) else 0,
   if (x ^^^ y) &&& xk &&& yk != 0 then -1 else if xk == -1 && yk == -1 then -1 else -1 <<< 1)
def zextF (srcW : Nat) (x k : I) : I × I :=
  let mask : I := ((1 : I) <<< srcW) - 1
  (x &&& mask, k ||| ~~~mask)
/-- two-argument Phi (the pass folds pairwise). -/
def phiF (a ak b bk : I) : I × I := (a, (ak &&& ~~~(a ^^^ b)) &&& bk)


-- ---------------------------------------------------------------- shifts (computeKnownBitsForShift)
-- doShiftByAConst for each op, with Go's int64/uint64 semantics for counts up to 64.
def lshV (x : I) (s : I) : I := x <<< s
def lshK (xk : I) (s : I) : I := (xk <<< s) ||| (((1 : I) <<< s) - 1)
def rshuV (w : Nat) (x : I) (s : I) : I := (x &&& (((1 : I) <<< w) - 1)) >>> s
def rshuK (w : Nat) (xk : I) (s : I) : I :=
  ((xk ||| ((-1 : I) <<< w)) >>> s) ||| ((~~~(0 : I)) <<< ((64 : I) - s))
def rshV (x : I) (s : I) : I := x.sshiftRight' s
def rshK (xk : I) (s : I) : I := xk.sshiftRight' s

/-- Closed form of `computeKnownBitsForShift`: the Go loop keeps the first value `v0` and
intersects `known &^= v0 ^ a; known &= k` over every candidate count; the first candidate
yielded by `allPossibleValues(y, yk')` is `y` itself (s = 0). `dv dk` is the shift-by-64 state,
`fv fk` the state for count `i`. -/
def shiftKnown (w : Nat) (fv fk : I → I) (y yk : I) (bounded : Bool) : I :=
  let dflt := !bounded && (BitVec.ofNat 64 w) ≤ ~~~yk
  let yk' := yk ||| ~~~(BitVec.ofNat 64 w - 1)
  let v0 := if dflt then fv 64 else fv y
  let base : I := if dflt then fk 64 else -1
  (List.range w).foldl (fun acc i =>
      if (BitVec.ofNat 64 i &&& yk') == y then acc &&& fk (BitVec.ofNat 64 i) &&& ~~~(v0 ^^^ fv (BitVec.ofNat 64 i))
      else acc) base
def shiftF (w : Nat) (fv fk : I → I) (y yk : I) (bounded : Bool) : I × I :=
  let big := (BitVec.ofNat 64 w) ≤ y
  let dflt := !bounded && (BitVec.ofNat 64 w) ≤ ~~~yk
  let v0 := if dflt then fv 64 else fv y
  let known := shiftKnown w fv fk y yk bounded
  (if big then fv 64 &&& fk 64 else v0 &&& known, if big then fk 64 else known)

macro "kb_shift" : tactic => `(tactic| simp only [rep, sx, inv, fits, norm, shiftF, shiftKnown, lshV, lshK, rshuV,
  rshuK, rshV, rshK, List.range, List.range.loop, List.foldl] at *)

-- ---------------------------------------------------------------- theorems, W = 8/16/32/64

macro "kb_unfold" : tactic => `(tactic| simp only [rep, sx, inv, fits, norm, normB, brep,
  andF, orF, xorF, comF, eqF, neqF, zextF, phiF] at *)

theorem and_sound_8 (a b : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a &&& b)) (norm 8 (andF x xk y yk)).1 (norm 8 (andF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem or_sound_8 (a b : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ||| b)) (norm 8 (orF x xk y yk)).1 (norm 8 (orF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem xor_sound_8 (a b : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ^^^ b)) (norm 8 (xorF x xk y yk)).1 (norm 8 (xorF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem com_sound_8 (a : BitVec 8) (x xk : I) (hx : inv 8 x xk) (ha : fits (rep a) x xk) :
    fits (rep (~~~a)) (norm 8 (comF x xk)).1 (norm 8 (comF x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem eq_sound_8 (a b : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a == b)) (normB (eqF x xk y yk)).1 (normB (eqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem neq_sound_8 (a b : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a != b)) (normB (neqF x xk y yk)).1 (normB (neqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem phi_sound_8 (a : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (h : fits (rep a) x xk ∨ fits (rep a) y yk) :
    fits (rep a) (norm 8 (phiF x xk y yk)).1 (norm 8 (phiF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, And: if every bit where `a` may be 1 is a known 1 of `b`, then `a & b = a`. -/
theorem simplify_and_8 (a b : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : (x ||| ~~~xk) &&& ~~~y = 0) :
    a &&& b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, Or: if every bit where `b` may be 1 is a known 1 of `a`, then `a | b = a`. -/
theorem simplify_or_8 (a b : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk) (hy : inv 8 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : ~~~x &&& (y ||| ~~~yk) = 0) :
    a ||| b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem and_sound_16 (a b : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a &&& b)) (norm 16 (andF x xk y yk)).1 (norm 16 (andF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem or_sound_16 (a b : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ||| b)) (norm 16 (orF x xk y yk)).1 (norm 16 (orF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem xor_sound_16 (a b : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ^^^ b)) (norm 16 (xorF x xk y yk)).1 (norm 16 (xorF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem com_sound_16 (a : BitVec 16) (x xk : I) (hx : inv 16 x xk) (ha : fits (rep a) x xk) :
    fits (rep (~~~a)) (norm 16 (comF x xk)).1 (norm 16 (comF x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem eq_sound_16 (a b : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a == b)) (normB (eqF x xk y yk)).1 (normB (eqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem neq_sound_16 (a b : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a != b)) (normB (neqF x xk y yk)).1 (normB (neqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem phi_sound_16 (a : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (h : fits (rep a) x xk ∨ fits (rep a) y yk) :
    fits (rep a) (norm 16 (phiF x xk y yk)).1 (norm 16 (phiF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, And: if every bit where `a` may be 1 is a known 1 of `b`, then `a & b = a`. -/
theorem simplify_and_16 (a b : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : (x ||| ~~~xk) &&& ~~~y = 0) :
    a &&& b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, Or: if every bit where `b` may be 1 is a known 1 of `a`, then `a | b = a`. -/
theorem simplify_or_16 (a b : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk) (hy : inv 16 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : ~~~x &&& (y ||| ~~~yk) = 0) :
    a ||| b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem and_sound_32 (a b : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a &&& b)) (norm 32 (andF x xk y yk)).1 (norm 32 (andF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem or_sound_32 (a b : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ||| b)) (norm 32 (orF x xk y yk)).1 (norm 32 (orF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem xor_sound_32 (a b : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ^^^ b)) (norm 32 (xorF x xk y yk)).1 (norm 32 (xorF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem com_sound_32 (a : BitVec 32) (x xk : I) (hx : inv 32 x xk) (ha : fits (rep a) x xk) :
    fits (rep (~~~a)) (norm 32 (comF x xk)).1 (norm 32 (comF x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem eq_sound_32 (a b : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a == b)) (normB (eqF x xk y yk)).1 (normB (eqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem neq_sound_32 (a b : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a != b)) (normB (neqF x xk y yk)).1 (normB (neqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem phi_sound_32 (a : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (h : fits (rep a) x xk ∨ fits (rep a) y yk) :
    fits (rep a) (norm 32 (phiF x xk y yk)).1 (norm 32 (phiF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, And: if every bit where `a` may be 1 is a known 1 of `b`, then `a & b = a`. -/
theorem simplify_and_32 (a b : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : (x ||| ~~~xk) &&& ~~~y = 0) :
    a &&& b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, Or: if every bit where `b` may be 1 is a known 1 of `a`, then `a | b = a`. -/
theorem simplify_or_32 (a b : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk) (hy : inv 32 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : ~~~x &&& (y ||| ~~~yk) = 0) :
    a ||| b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem and_sound_64 (a b : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a &&& b)) (norm 64 (andF x xk y yk)).1 (norm 64 (andF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem or_sound_64 (a b : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ||| b)) (norm 64 (orF x xk y yk)).1 (norm 64 (orF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem xor_sound_64 (a b : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (rep (a ^^^ b)) (norm 64 (xorF x xk y yk)).1 (norm 64 (xorF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem com_sound_64 (a : BitVec 64) (x xk : I) (hx : inv 64 x xk) (ha : fits (rep a) x xk) :
    fits (rep (~~~a)) (norm 64 (comF x xk)).1 (norm 64 (comF x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem eq_sound_64 (a b : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a == b)) (normB (eqF x xk y yk)).1 (normB (eqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem neq_sound_64 (a b : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) :
    fits (brep (a != b)) (normB (neqF x xk y yk)).1 (normB (neqF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem phi_sound_64 (a : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (h : fits (rep a) x xk ∨ fits (rep a) y yk) :
    fits (rep a) (norm 64 (phiF x xk y yk)).1 (norm 64 (phiF x xk y yk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, And: if every bit where `a` may be 1 is a known 1 of `b`, then `a & b = a`. -/
theorem simplify_and_64 (a b : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : (x ||| ~~~xk) &&& ~~~y = 0) :
    a &&& b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
/-- simplifyValue, Or: if every bit where `b` may be 1 is a known 1 of `a`, then `a | b = a`. -/
theorem simplify_or_64 (a b : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk) (hy : inv 64 y yk)
    (ha : fits (rep a) x xk) (hb : fits (rep b) y yk) (hc : ~~~x &&& (y ||| ~~~yk) = 0) :
    a ||| b = a := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem zext_sound_8_16 (a : BitVec 8) (x xk : I) (hx : inv 8 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 16)) (norm 16 (zextF 8 x xk)).1 (norm 16 (zextF 8 x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem sext_sound_8_16 (a : BitVec 8) (x xk : I) (hx : inv 8 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.signExtend 16)) (norm 16 (x, xk)).1 (norm 16 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem trunc_sound_16_8 (a : BitVec 16) (x xk : I) (hx : inv 16 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 8)) (norm 8 (x, xk)).1 (norm 8 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem zext_sound_8_32 (a : BitVec 8) (x xk : I) (hx : inv 8 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 32)) (norm 32 (zextF 8 x xk)).1 (norm 32 (zextF 8 x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem sext_sound_8_32 (a : BitVec 8) (x xk : I) (hx : inv 8 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.signExtend 32)) (norm 32 (x, xk)).1 (norm 32 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem trunc_sound_32_8 (a : BitVec 32) (x xk : I) (hx : inv 32 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 8)) (norm 8 (x, xk)).1 (norm 8 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem zext_sound_8_64 (a : BitVec 8) (x xk : I) (hx : inv 8 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 64)) (norm 64 (zextF 8 x xk)).1 (norm 64 (zextF 8 x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem sext_sound_8_64 (a : BitVec 8) (x xk : I) (hx : inv 8 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.signExtend 64)) (norm 64 (x, xk)).1 (norm 64 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem trunc_sound_64_8 (a : BitVec 64) (x xk : I) (hx : inv 64 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 8)) (norm 8 (x, xk)).1 (norm 8 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem zext_sound_16_32 (a : BitVec 16) (x xk : I) (hx : inv 16 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 32)) (norm 32 (zextF 16 x xk)).1 (norm 32 (zextF 16 x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem sext_sound_16_32 (a : BitVec 16) (x xk : I) (hx : inv 16 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.signExtend 32)) (norm 32 (x, xk)).1 (norm 32 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem trunc_sound_32_16 (a : BitVec 32) (x xk : I) (hx : inv 32 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 16)) (norm 16 (x, xk)).1 (norm 16 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem zext_sound_16_64 (a : BitVec 16) (x xk : I) (hx : inv 16 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 64)) (norm 64 (zextF 16 x xk)).1 (norm 64 (zextF 16 x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem sext_sound_16_64 (a : BitVec 16) (x xk : I) (hx : inv 16 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.signExtend 64)) (norm 64 (x, xk)).1 (norm 64 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem trunc_sound_64_16 (a : BitVec 64) (x xk : I) (hx : inv 64 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 16)) (norm 16 (x, xk)).1 (norm 16 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem zext_sound_32_64 (a : BitVec 32) (x xk : I) (hx : inv 32 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 64)) (norm 64 (zextF 32 x xk)).1 (norm 64 (zextF 32 x xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem sext_sound_32_64 (a : BitVec 32) (x xk : I) (hx : inv 32 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.signExtend 64)) (norm 64 (x, xk)).1 (norm 64 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem trunc_sound_64_32 (a : BitVec 64) (x xk : I) (hx : inv 64 x xk) (ha : fits (rep a) x xk) :
    fits (rep (a.setWidth 32)) (norm 32 (x, xk)).1 (norm 32 (x, xk)).2 := by
  kb_unfold; bv_decide (config := {timeout := 120})
theorem lsh_8x8_unbounded (a : BitVec 8) (c : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_8x8_bounded (a : BitVec 8) (c : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#8) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x8_unbounded (a : BitVec 8) (c : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x8_bounded (a : BitVec 8) (c : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#8) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x8_unbounded (a : BitVec 8) (c : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x8_bounded (a : BitVec 8) (c : BitVec 8) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#8) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_8x16_unbounded (a : BitVec 8) (c : BitVec 16) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_8x16_bounded (a : BitVec 8) (c : BitVec 16) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#16) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x16_unbounded (a : BitVec 8) (c : BitVec 16) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x16_bounded (a : BitVec 8) (c : BitVec 16) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#16) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x16_unbounded (a : BitVec 8) (c : BitVec 16) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x16_bounded (a : BitVec 8) (c : BitVec 16) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#16) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_8x32_unbounded (a : BitVec 8) (c : BitVec 32) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_8x32_bounded (a : BitVec 8) (c : BitVec 32) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#32) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x32_unbounded (a : BitVec 8) (c : BitVec 32) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x32_bounded (a : BitVec 8) (c : BitVec 32) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#32) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x32_unbounded (a : BitVec 8) (c : BitVec 32) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x32_bounded (a : BitVec 8) (c : BitVec 32) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#32) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_8x64_unbounded (a : BitVec 8) (c : BitVec 64) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_8x64_bounded (a : BitVec 8) (c : BitVec 64) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#64) :
    fits (rep (a <<< c)) (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).1
      (norm 8 (shiftF 8 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x64_unbounded (a : BitVec 8) (c : BitVec 64) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_8x64_bounded (a : BitVec 8) (c : BitVec 64) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#64) :
    fits (rep (a >>> c)) (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).1
      (norm 8 (shiftF 8 (rshuV 8 x) (rshuK 8 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x64_unbounded (a : BitVec 8) (c : BitVec 64) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_8x64_bounded (a : BitVec 8) (c : BitVec 64) (x xk y yk : I) (hx : inv 8 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 8#64) :
    fits (rep (a.sshiftRight' c)) (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).1
      (norm 8 (shiftF 8 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x8_unbounded (a : BitVec 16) (c : BitVec 8) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x8_bounded (a : BitVec 16) (c : BitVec 8) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#8) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x8_unbounded (a : BitVec 16) (c : BitVec 8) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x8_bounded (a : BitVec 16) (c : BitVec 8) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#8) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x8_unbounded (a : BitVec 16) (c : BitVec 8) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x8_bounded (a : BitVec 16) (c : BitVec 8) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#8) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x16_unbounded (a : BitVec 16) (c : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x16_bounded (a : BitVec 16) (c : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#16) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x16_unbounded (a : BitVec 16) (c : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x16_bounded (a : BitVec 16) (c : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#16) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x16_unbounded (a : BitVec 16) (c : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x16_bounded (a : BitVec 16) (c : BitVec 16) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#16) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x32_unbounded (a : BitVec 16) (c : BitVec 32) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x32_bounded (a : BitVec 16) (c : BitVec 32) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#32) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x32_unbounded (a : BitVec 16) (c : BitVec 32) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x32_bounded (a : BitVec 16) (c : BitVec 32) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#32) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x32_unbounded (a : BitVec 16) (c : BitVec 32) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x32_bounded (a : BitVec 16) (c : BitVec 32) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#32) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x64_unbounded (a : BitVec 16) (c : BitVec 64) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_16x64_bounded (a : BitVec 16) (c : BitVec 64) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#64) :
    fits (rep (a <<< c)) (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).1
      (norm 16 (shiftF 16 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x64_unbounded (a : BitVec 16) (c : BitVec 64) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_16x64_bounded (a : BitVec 16) (c : BitVec 64) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#64) :
    fits (rep (a >>> c)) (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).1
      (norm 16 (shiftF 16 (rshuV 16 x) (rshuK 16 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x64_unbounded (a : BitVec 16) (c : BitVec 64) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_16x64_bounded (a : BitVec 16) (c : BitVec 64) (x xk y yk : I) (hx : inv 16 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 16#64) :
    fits (rep (a.sshiftRight' c)) (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).1
      (norm 16 (shiftF 16 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x8_unbounded (a : BitVec 32) (c : BitVec 8) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x8_bounded (a : BitVec 32) (c : BitVec 8) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#8) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x8_unbounded (a : BitVec 32) (c : BitVec 8) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x8_bounded (a : BitVec 32) (c : BitVec 8) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#8) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x8_unbounded (a : BitVec 32) (c : BitVec 8) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x8_bounded (a : BitVec 32) (c : BitVec 8) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#8) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x16_unbounded (a : BitVec 32) (c : BitVec 16) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x16_bounded (a : BitVec 32) (c : BitVec 16) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#16) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x16_unbounded (a : BitVec 32) (c : BitVec 16) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x16_bounded (a : BitVec 32) (c : BitVec 16) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#16) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x16_unbounded (a : BitVec 32) (c : BitVec 16) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x16_bounded (a : BitVec 32) (c : BitVec 16) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#16) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x32_unbounded (a : BitVec 32) (c : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x32_bounded (a : BitVec 32) (c : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#32) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x32_unbounded (a : BitVec 32) (c : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x32_bounded (a : BitVec 32) (c : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#32) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x32_unbounded (a : BitVec 32) (c : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x32_bounded (a : BitVec 32) (c : BitVec 32) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#32) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x64_unbounded (a : BitVec 32) (c : BitVec 64) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_32x64_bounded (a : BitVec 32) (c : BitVec 64) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#64) :
    fits (rep (a <<< c)) (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).1
      (norm 32 (shiftF 32 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x64_unbounded (a : BitVec 32) (c : BitVec 64) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_32x64_bounded (a : BitVec 32) (c : BitVec 64) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#64) :
    fits (rep (a >>> c)) (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).1
      (norm 32 (shiftF 32 (rshuV 32 x) (rshuK 32 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x64_unbounded (a : BitVec 32) (c : BitVec 64) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_32x64_bounded (a : BitVec 32) (c : BitVec 64) (x xk y yk : I) (hx : inv 32 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 32#64) :
    fits (rep (a.sshiftRight' c)) (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).1
      (norm 32 (shiftF 32 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_64x8_unbounded (a : BitVec 64) (c : BitVec 8) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_64x8_bounded (a : BitVec 64) (c : BitVec 8) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#8) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_64x8_unbounded (a : BitVec 64) (c : BitVec 8) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 600})
theorem rshu_64x8_bounded (a : BitVec 64) (c : BitVec 8) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#8) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_64x8_unbounded (a : BitVec 64) (c : BitVec 8) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_64x8_bounded (a : BitVec 64) (c : BitVec 8) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 8 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#8) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_64x16_unbounded (a : BitVec 64) (c : BitVec 16) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_64x16_bounded (a : BitVec 64) (c : BitVec 16) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#16) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_64x16_unbounded (a : BitVec 64) (c : BitVec 16) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 600})
theorem rshu_64x16_bounded (a : BitVec 64) (c : BitVec 16) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#16) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_64x16_unbounded (a : BitVec 64) (c : BitVec 16) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 600})
theorem rsh_64x16_bounded (a : BitVec 64) (c : BitVec 16) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 16 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#16) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_64x32_unbounded (a : BitVec 64) (c : BitVec 32) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 600})
theorem lsh_64x32_bounded (a : BitVec 64) (c : BitVec 32) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#32) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_64x32_unbounded (a : BitVec 64) (c : BitVec 32) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 600})
theorem rshu_64x32_bounded (a : BitVec 64) (c : BitVec 32) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#32) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_64x32_unbounded (a : BitVec 64) (c : BitVec 32) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 600})
theorem rsh_64x32_bounded (a : BitVec 64) (c : BitVec 32) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 32 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#32) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_64x64_unbounded (a : BitVec 64) (c : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem lsh_64x64_bounded (a : BitVec 64) (c : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#64) :
    fits (rep (a <<< c)) (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).1
      (norm 64 (shiftF 64 (lshV x) (lshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_64x64_unbounded (a : BitVec 64) (c : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rshu_64x64_bounded (a : BitVec 64) (c : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#64) :
    fits (rep (a >>> c)) (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).1
      (norm 64 (shiftF 64 (rshuV 64 x) (rshuK 64 xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_64x64_unbounded (a : BitVec 64) (c : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk false)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
theorem rsh_64x64_bounded (a : BitVec 64) (c : BitVec 64) (x xk y yk : I) (hx : inv 64 x xk)
    (hy : inv 64 y yk) (ha : fits (rep a) x xk) (hc : fits (rep c) y yk)
    (hbd : c < 64#64) :
    fits (rep (a.sshiftRight' c)) (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).1
      (norm 64 (shiftF 64 (rshV x) (rshK xk) y yk true)).2 := by
  kb_shift; bv_decide (config := {timeout := 120})
end Go.Compiler.KnownBits
