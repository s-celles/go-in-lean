import GoInLean.Semantics.Int
/-!
# Semantics of the generic SSA value operations used by constant folding

Hand-written from `src/cmd/compile/internal/ssa/_gen/genericOps.go` (go1.25.5):
`AddN`, `SubN`, `MulN`, `AndN`, `OrN`, `XorN` are two's-complement; `DivN`/`ModN`
are signed truncated, `DivNu`/`ModNu` unsigned ("arg0 / arg1, signed/unsigned");
`NegN`, `ComN` (bitwise complement); `LshNx64`, `RshNx64` (arithmetic),
`RshNUx64` (logical) with a 64-bit shift amount "considered unsigned", and
`TruncAtoB`, `ZeroExtAtoB`, `SignExtAtoB`. Shift amounts `≥ N` give 0 or the sign
fill, as in Go source semantics (the generic ops are defined to have Go's
semantics; the per-architecture lowering inserts the masking).

The generated file `GeneratedFolds.lean` states, for every constant-folding
rule of `generic.rules` recognised by `scripts/rules_to_lean.py`, that the
rule's right-hand side, translated under Go's typed-integer semantics
(`auxIntToIntN`/`intNToAuxInt`, so arithmetic is done at width N), equals
the operation below applied to the operands.
-/
namespace Go.Compiler.OpSem

def add {w} (a b : BitVec w) : BitVec w := a + b
def sub {w} (a b : BitVec w) : BitVec w := a - b
def mul {w} (a b : BitVec w) : BitVec w := a * b
def and {w} (a b : BitVec w) : BitVec w := a &&& b
def or  {w} (a b : BitVec w) : BitVec w := a ||| b
def xor {w} (a b : BitVec w) : BitVec w := a ^^^ b
/-- `DivN` (signed, truncated); the rule requires `d != 0`. -/
def div {w} (a b : BitVec w) : BitVec w := a.sdiv b
def mod {w} (a b : BitVec w) : BitVec w := a.srem b
def divu {w} (a b : BitVec w) : BitVec w := a / b
def modu {w} (a b : BitVec w) : BitVec w := a % b
def neg {w} (a : BitVec w) : BitVec w := -a
def com {w} (a : BitVec w) : BitVec w := ~~~a
/-- `LshNx64 a s`: shift amount is an unsigned 64-bit value. -/
def lsh {w} (a : BitVec w) (s : BitVec 64) : BitVec w := a <<< s.toNat
def rsh {w} (a : BitVec w) (s : BitVec 64) : BitVec w := a.sshiftRight s.toNat
def rshu {w} (a : BitVec w) (s : BitVec 64) : BitVec w := a >>> s.toNat
def trunc {w} (v : Nat) (a : BitVec w) : BitVec v := a.setWidth v
def zeroExt {w} (v : Nat) (a : BitVec w) : BitVec v := a.setWidth v
def signExt {w} (v : Nat) (a : BitVec w) : BitVec v := a.signExtend v

end Go.Compiler.OpSem
