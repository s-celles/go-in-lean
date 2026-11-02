import Std.Tactic.BVDecide
/-!
# arm64: constant-flag folding of CSINV yields a boolean `Not` (finding ARM64-CSINV-NOT)

`ARM64.rules` (go1.21 .. master `babb75be`):

    (CSNEG [cc] _ y flag) && ccARM64Eval(cc, flag) < 0 => (NEG y)
    (CSINV [cc] _ y flag) && ccARM64Eval(cc, flag) < 0 => (Not y)
    (CSINC [cc] _ y flag) && ccARM64Eval(cc, flag) < 0 => (ADDconst [1] y)

`CSINV cc x y` selects `x` if `cc` holds and the bitwise complement `^y` otherwise. When the flags
are a known constant and `cc` is false, the rule produces the generic op `Not`, which is the
*boolean* negation and is lowered by `(Not x) => (XOR (MOVDconst [1]) x)`. The result is `y ^ 1`
instead of `^y`. Fix: `(MVN y)`. The CSNEG and CSINC siblings are correct.
-/
namespace Go.Compiler.ARM64CondSelect

def csinv (cc : Bool) (x y : BitVec 64) : BitVec 64 := if cc then x else ~~~y
def csneg (cc : Bool) (x y : BitVec 64) : BitVec 64 := if cc then x else -y
def csinc (cc : Bool) (x y : BitVec 64) : BitVec 64 := if cc then x else y + 1
/-- `(Not x) => (XOR (MOVDconst [1]) x)` on arm64. -/
def notLowered (y : BitVec 64) : BitVec 64 := y ^^^ 1

/-- The current rule: `^2 = -3`, but `Not 2` lowers to `3`. -/
theorem csinv_not_refuted : csinv false 0 2 = -3 ∧ notLowered 2 = 3 := by decide

theorem csinv_not_unsound : ¬ ∀ x y, csinv false x y = notLowered y := by
  intro h; have := h 0 2; revert this; decide

/-- Fix: `MVN y` is the complement. -/
theorem csinv_mvn_fixed (x y : BitVec 64) : csinv false x y = ~~~y := rfl

theorem csinv_true (x y : BitVec 64) : csinv true x y = x := rfl
theorem csneg_false (x y : BitVec 64) : csneg false x y = -y := rfl
theorem csinc_false (x y : BitVec 64) : csinc false x y = y + 1 := rfl

/-- The lowered `Not` and `MVN` never agree. -/
theorem not_ne_mvn (y : BitVec 64) : notLowered y ≠ ~~~y := by
  unfold notLowered; bv_decide (config := {timeout := 120})

end Go.Compiler.ARM64CondSelect
