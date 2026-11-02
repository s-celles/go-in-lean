import Std.Tactic.BVDecide
/-!
# Latent: rotate recognition with a huge shift count (generic.rules:2220-2223 on master)

`((Add64|Or64|Xor64) (Lsh64x64 x z:(Const64 [c])) (Rsh64Ux64 x (Const64 [d]))) && c < 64 && d == 64-c
 && canRotate(config, 64) => (RotateLeft64 x z)` uses the SIGNED test `c < 64`: a count
`c ≥ 2^63` passes it. Go semantics give `x << c = 0` and `x >> (64-c) = 0`; the rotate does not.
Unreachable in practice: `(Lsh64x64 _ (Const64 [c])) && uint64(c) >= 64 => 0` (generic.rules
446-449 in go1.25.5) rewrites the inner shift first, because the shift value precedes its
use in rewrite order. Checked with go1.27.3 and master `babb75be` (correct results).
`rotl` is the rotation by the low 6 bits of the count (genericOps.go RotateLeft64).
-/
namespace Go.Compiler.LatentRotate

def rotl (x k : BitVec 64) : BitVec 64 :=
  (x <<< (k &&& 63)) ||| (x >>> ((64 - (k &&& 63)) &&& 63))

/-- Sound when the count is a genuine small value (`0 ≤ c < 64`). -/
theorem rotate_sound (x c d : BitVec 64) (hc : c < 64) (hd : d = 64 - c) :
    (x <<< c) ||| (x >>> d) = rotl x c := by
  unfold rotl; bv_decide (config := {timeout := 120})

/-- Refuted for the count `2^64-1` admitted by the signed test (x = 1, d = 65). -/
theorem rotate_hugeCount_counterexample (x c d : BitVec 64) (hx : x = 1)
    (hc : c = 0xFFFFFFFFFFFFFFFF) (hd : d = 64 - c) :
    c.slt 64 = true ∧ (x <<< c) ||| (x >>> d) ≠ rotl x c := by
  unfold rotl; bv_decide (config := {timeout := 120})

end Go.Compiler.LatentRotate
