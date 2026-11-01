/-!
# Go fixed-width integer semantics

Reference: The Go Programming Language Specification (go1.25),
sections "Numeric types", "Integer operators", "Arithmetic operators",
"Integer overflow", "Conversions".

Design:
* Every Go integer type of width `w` is represented by `BitVec w`.
  Signedness is a property of the *operation*, not of the value, exactly as
  in two's-complement hardware. `uint8 … uint64` and `int8 … int64` are
  type aliases so that the Lean code reads like the Go code.
* `int` and `uint` are fixed to 64 bits (see `docs/semantic-boundary.md`,
  assumption A1). Go only guarantees ≥ 32 bits; the proofs in this
  repository are therefore about 64-bit targets (amd64, arm64, …).
* Operations that panic in Go (`/` and `%` by zero, negative shift counts)
  return `Except Panic _`. Operations that silently wrap (`+ - *`, shifts,
  conversions) are total and use the core `BitVec` functions, whose
  semantics were checked against Go in `go/tests/semantics_test.go`.

Nothing here is axiomatised; all definitions are computable.
-/

namespace Go

/-- The run-time panics relevant to the modelled subset. -/
inductive Panic where
  | divideError        -- "integer divide by zero"
  | overflowError      -- "integer overflow" (math/bits.Div quotient overflow)
  | negativeShift      -- "negative shift amount"
  | indexOutOfRange    -- "index out of range"
  | message (s : String)
  deriving Repr, DecidableEq

instance {ε α : Type} [DecidableEq ε] [DecidableEq α] : DecidableEq (Except ε α) := fun
  | .ok a, .ok b => if h : a = b then isTrue (by simp [h]) else isFalse (by simp [h])
  | .error a, .error b => if h : a = b then isTrue (by simp [h]) else isFalse (by simp [h])
  | .ok _, .error _ => isFalse (by simp)
  | .error _, .ok _ => isFalse (by simp)

abbrev uint8  := BitVec 8
abbrev uint16 := BitVec 16
abbrev uint32 := BitVec 32
abbrev uint64 := BitVec 64
abbrev int8   := BitVec 8
abbrev int16  := BitVec 16
abbrev int32  := BitVec 32
abbrev int64  := BitVec 64

/-- Spec: "the size of a uint in bits" — fixed to 64 here (assumption A1). -/
abbrev UintSize : Nat := 64
abbrev uint := BitVec UintSize
abbrev int  := BitVec UintSize

/-- `math.MaxInt` on a 64-bit target, as `uint` (used by strings/bytes/slices.Repeat). -/
def maxInt : uint := (1#64 <<< 63) - 1

/-! ## Shifts (spec: "The shift operators shift the left operand by the shift
count specified by the right operand, which must be non-negative … There is
no upper limit on the shift count. Shifts behave as if the left operand is
shifted n times by 1".) Core `BitVec` shifts by a `Nat` already yield `0`
(or the sign fill) once the count reaches the width. -/

/-- `x << s` with an unsigned count. -/
def shl {w v : Nat} (x : BitVec w) (s : BitVec v) : BitVec w := x <<< s.toNat
/-- `x >> s` on an unsigned operand (logical shift). -/
def shrU {w v : Nat} (x : BitVec w) (s : BitVec v) : BitVec w := x >>> s.toNat
/-- `x >> s` on a signed operand (arithmetic shift, sign fill for large counts). -/
def shrS {w v : Nat} (x : BitVec w) (s : BitVec v) : BitVec w := x.sshiftRight s.toNat

/-- Shift with a *signed* count: since Go 1.13 a negative count panics at run time. -/
def shlSigned {w v : Nat} (x : BitVec w) (s : BitVec v) : Except Panic (BitVec w) :=
  if s.msb then .error .negativeShift else .ok (x <<< s.toNat)
def shrUSigned {w v : Nat} (x : BitVec w) (s : BitVec v) : Except Panic (BitVec w) :=
  if s.msb then .error .negativeShift else .ok (x >>> s.toNat)

/-! ## Division (spec: "if the divisor is a constant, it must not be zero. If
the divisor is zero at run time, a run-time panic occurs … q = x / y with
truncated division; x = q*y + r with |r| < |y|; if the dividend x is the most
negative value for the int type of x, the quotient q = x / -1 is equal to x
(and r = 0) due to two's-complement integer overflow"). Core `BitVec.sdiv`
and `BitVec.srem` are truncating and satisfy the MinInt / -1 clause, see
`Go.Semantics.Validation`. -/

def divU {w : Nat} (x y : BitVec w) : Except Panic (BitVec w) :=
  if y = 0 then .error .divideError else .ok (x / y)
def remU {w : Nat} (x y : BitVec w) : Except Panic (BitVec w) :=
  if y = 0 then .error .divideError else .ok (x % y)
def divS {w : Nat} (x y : BitVec w) : Except Panic (BitVec w) :=
  if y = 0 then .error .divideError else .ok (x.sdiv y)
def remS {w : Nat} (x y : BitVec w) : Except Panic (BitVec w) :=
  if y = 0 then .error .divideError else .ok (x.srem y)

/-! ## Conversions (spec: "When converting between integer types, if the value
is a signed integer, it is sign extended to implicit infinite precision;
otherwise it is zero extended. It is then truncated to fit in the result
type's size.") -/

/-- Conversion from an unsigned source type to any integer type of width `v`. -/
def convU {w : Nat} (v : Nat) (x : BitVec w) : BitVec v := x.setWidth v
/-- Conversion from a signed source type to any integer type of width `v`. -/
def convS {w : Nat} (v : Nat) (x : BitVec w) : BitVec v := x.signExtend v

/-! ## Comparisons: unsigned comparisons are the core `<`/`≤` on `BitVec`;
signed ones are `slt`/`sle`. Exposed under Go-like names for readability. -/
def ltU {w : Nat} (x y : BitVec w) : Bool := x < y
def leU {w : Nat} (x y : BitVec w) : Bool := x ≤ y
def ltS {w : Nat} (x y : BitVec w) : Bool := x.slt y
def leS {w : Nat} (x y : BitVec w) : Bool := x.sle y

/-- `&^` (AND NOT, "bit clear"). -/
def andNot {w : Nat} (x y : BitVec w) : BitVec w := x &&& ~~~y

end Go
