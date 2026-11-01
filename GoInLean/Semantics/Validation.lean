import Std.Tactic.BVDecide
import GoInLean.Semantics.Int
/-!
# Validation of the integer semantics against the Go specification

These are *executable* checks of the Lean primitives against values obtained
by running the pinned Go toolchain (`go/tests/semantics_test.go` prints the
same table). They guard against a silent divergence between Lean's `BitVec`
library and Go's integer semantics. Every statement is checked by `decide`
(kernel evaluation); native evaluation is never used.
-/
namespace Go.Semantics.Validation

-- Truncated signed division and remainder (Go: -7/2 == -3, -7%2 == -1).
example : (BitVec.ofInt 8 (-7)).sdiv 2 = BitVec.ofInt 8 (-3) := by decide
example : (BitVec.ofInt 8 (-7)).srem 2 = BitVec.ofInt 8 (-1) := by decide
-- MinInt8 / -1 == MinInt8, MinInt8 % -1 == 0 (no panic in Go).
example : (BitVec.ofInt 8 (-128)).sdiv (BitVec.ofInt 8 (-1)) = BitVec.ofInt 8 (-128) := by decide
example : (BitVec.ofInt 8 (-128)).srem (BitVec.ofInt 8 (-1)) = 0 := by decide
-- Shifts by at least the width: uint8(5)<<10 == 0, uint8(5)>>10 == 0, int8(-1)>>10 == -1.
example : Go.shl (5 : uint8) (10 : uint) = 0 := by decide
example : Go.shrU (5 : uint8) (10 : uint) = 0 := by decide
example : Go.shrS (BitVec.ofInt 8 (-1)) (10 : uint) = BitVec.ofInt 8 (-1) := by decide
-- Negative signed shift count panics.
example : Go.shlSigned (5 : uint8) (BitVec.ofInt 64 (-1)) = .error .negativeShift := by decide
-- Conversions: uint8(300) == 44, int8(uint8(200)) == -56, uint64(int8(-1)) == MaxUint64.
example : Go.convU 8 (300 : BitVec 16) = 44 := by decide
example : Go.convS 8 (200 : uint8) = BitVec.ofInt 8 (-56) := by decide
example : Go.convS 64 (BitVec.ofInt 8 (-1)) = BitVec.ofInt 64 (-1) := by decide
-- Division by zero panics for every width-8 dividend (exhaustive).
example : ∀ x : uint8, Go.divU x 0 = .error .divideError := by decide
example : ∀ x : int8, Go.divS x 0 = .error .divideError := by decide
-- General: the spec's division identity x = q*y + r for all 8-bit signed pairs, y ≠ 0.
theorem sdiv_srem_identity (x y : int8) (h : y ≠ 0) : x = (x.sdiv y) * y + x.srem y := by
  bv_decide
theorem udiv_umod_identity (x y : uint8) (h : y ≠ 0) : x = (x / y) * y + x % y := by
  bv_decide
example : Go.maxInt = 0x7FFFFFFFFFFFFFFF := by decide

end Go.Semantics.Validation
