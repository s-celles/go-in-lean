import GoInLean.Semantics.BitSpec
/-!
# Value semantics of generic SSA integer ops and of the `rewrite.go` helpers used in rule
# conditions, for the rule translator `scripts/generic_rules_to_lean.py`

All definitions are bit-blastable after unfolding (`BitSpec.len/ctz/clz` are unrolled folds).
Helpers (rewrite.go, go1.25.5): `isPowerOfTwo(n) = n > 0 && n&(n-1) == 0`,
`logN(n) = int64(bits.LenN(uintN(n))) - 1`, `ntzN`/`nlzN` = trailing/leading zeros as `int`,
`oneBit(x) = x&(x-1) == 0 && x != 0`, `uaddOvf(a,b) = uint64(a)+uint64(b) < uint64(a)`,
`is32Bit(n) = n == int64(int32(n))`.
-/
namespace Go.Compiler.GSem

def isPowerOfTwo {w : Nat} (n : BitVec w) : Bool := (0#w).slt n && (n &&& (n - 1)) == 0
def lg {w : Nat} (n : BitVec w) : BitVec 64 := BitSpec.len n - 1
def ntz {w : Nat} (n : BitVec w) : BitVec 64 := BitSpec.ctz n
def nlz {w : Nat} (n : BitVec w) : BitVec 64 := BitSpec.clz n
def oneBit {w : Nat} (x : BitVec w) : Bool := (x &&& (x - 1)) == 0 && x != 0
def uaddOvf (a b : BitVec 64) : Bool := a + b < a
def is32Bit (n : BitVec 64) : Bool := n == (n.setWidth 32).signExtend 64
def b2i (b : Bool) : BitVec 64 := if b then 1 else 0
/-- `bits.ReverseBytesN`: byte reversal by concatenation (w a multiple of 8). -/
def revBytes {w : Nat} (x : BitVec w) : BitVec w :=
  ((List.range (w / 8)).foldl (fun acc i => acc ||| (((x >>> (8 * i)) &&& 0xff) <<< (w - 8 - 8 * i))) 0)

end Go.Compiler.GSem
