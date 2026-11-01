import GoInLean.Semantics.Int
/-!
# Reference specifications for bit-level functions

These definitions are the *oracle*: deliberately naive, written as unrolled
folds over the bit positions so that they are (a) obviously correct by
inspection and (b) bit-blastable by `bv_decide` after `simp` unrolls the
`List.range`. They are independent of the Go implementations in
`GoInLean.Stdlib.Bits`.
-/
namespace Go.BitSpec

/-- Number of bits needed to represent `x` (0 for 0): 1 + index of the highest set bit. -/
def len {w : Nat} (x : BitVec w) : BitVec 64 :=
  (List.range w).foldl (fun acc i => if x.getLsbD i then BitVec.ofNat 64 (i+1) else acc) 0

/-- Count of leading zero bits (`w` for 0). -/
def clz {w : Nat} (x : BitVec w) : BitVec 64 := BitVec.ofNat 64 w - len x

/-- Count of leading zero bits, as a value of the *same* width (`w` for 0). Used
inside `Div64`'s model for the normalisation shift so that every shift amount has the
machine width, as in Go. `clzW_eq_clz` relates it to `clz`. -/
def clzW {w : Nat} (x : BitVec w) : BitVec w :=
  (List.range w).foldl (fun acc i => if x.getLsbD i then BitVec.ofNat w (w - 1 - i) else acc) (BitVec.ofNat w w)

/-- Count of trailing zero bits (`w` for 0): index of the lowest set bit. -/
def ctz {w : Nat} (x : BitVec w) : BitVec 64 :=
  (List.range w).foldr (fun i acc => if x.getLsbD i then BitVec.ofNat 64 i else acc) (BitVec.ofNat 64 w)

/-- Population count. -/
def popcount {w : Nat} (x : BitVec w) : BitVec 64 :=
  (List.range w).foldl (fun acc i => acc + (if x.getLsbD i then 1 else 0)) 0

/-- Bit reversal: bit `i` of the result is bit `w-1-i` of `x`. -/
def reverse {w : Nat} (x : BitVec w) : BitVec w :=
  (List.range w).foldl (fun acc i => if x.getLsbD (w - 1 - i) then acc ||| (1 <<< i) else acc) 0

/-- Byte reversal for a width that is a multiple of 8, as concatenation of the bytes
in reverse order (`++` puts its first argument in the high bits). -/
def reverseBytes16 (x : BitVec 16) : BitVec 16 := x.extractLsb' 0 8 ++ x.extractLsb' 8 8
def reverseBytes32 (x : BitVec 32) : BitVec 32 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8
def reverseBytes64 (x : BitVec 64) : BitVec 64 :=
  x.extractLsb' 0 8 ++ x.extractLsb' 8 8 ++ x.extractLsb' 16 8 ++ x.extractLsb' 24 8 ++
  x.extractLsb' 32 8 ++ x.extractLsb' 40 8 ++ x.extractLsb' 48 8 ++ x.extractLsb' 56 8

end Go.BitSpec
