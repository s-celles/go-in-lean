import Lean.Data.Json
import GoInLean.Stdlib.Bits
/-!
# Differential check of the Lean models against Go-produced vectors

`lake exe checkvectors targets/vectors/bits.json` evaluates every Lean model
on the inputs recorded by `go/tests/vectors/gen_vectors.go` (run with the
pinned Go toolchain) and fails if any output differs. This validates the
*model* against the *implementation*; it is not a proof and uses the
compiled evaluator, not the kernel.
-/
open Lean Go Go.Bits

structure Vec where
  fn : String
  inp : Array Nat
  out : Option (Array Nat)
  panic : Option String
  deriving Repr

def parseVec (j : Json) : Except String Vec := do
  let fn ← j.getObjValAs? String "fn"
  let inp ← j.getObjValAs? (Array Nat) "in"
  let out := (j.getObjValAs? (Array Nat) "out").toOption
  let panic := (j.getObjValAs? String "panic").toOption
  pure { fn, inp, out, panic }

def panicName : Panic → String
  | .divideError => "divideError"
  | .overflowError => "overflowError"
  | .negativeShift => "negativeShift"
  | .indexOutOfRange => "indexOutOfRange"
  | .message s => "other: " ++ s

def bv (w : Nat) (n : Nat) : BitVec w := BitVec.ofNat w n

def one {w : Nat} (x : BitVec w) : Except String (Array Nat) := .ok #[x.toNat]
def two {w w' : Nat} (p : BitVec w × BitVec w') : Except String (Array Nat) := .ok #[p.1.toNat, p.2.toNat]
def ex {w w' : Nat} (e : Except Panic (BitVec w × BitVec w')) : Except String (Array Nat) :=
  match e with | .ok p => two p | .error p => .error (panicName p)
def ex1 {w : Nat} (e : Except Panic (BitVec w)) : Except String (Array Nat) :=
  match e with | .ok p => one p | .error p => .error (panicName p)

/-- Returns `.ok outputs` or `.error panicName`, or `none` if the function is unknown. -/
def eval (v : Vec) : Option (Except String (Array Nat)) :=
  let a := v.inp
  let g (i : Nat) : Nat := a.getD i 0
  match v.fn with
  | "Len8" => one (Len8 (bv 8 (g 0))) | "Len16" => one (Len16 (bv 16 (g 0)))
  | "Len32" => one (Len32 (bv 32 (g 0))) | "Len64" => one (Len64 (bv 64 (g 0)))
  | "LeadingZeros64" => one (LeadingZeros64 (bv 64 (g 0)))
  | "TrailingZeros8" => one (TrailingZeros8 (bv 8 (g 0)))
  | "TrailingZeros16" => one (TrailingZeros16 (bv 16 (g 0)))
  | "TrailingZeros32" => one (TrailingZeros32 (bv 32 (g 0)))
  | "TrailingZeros64" => one (TrailingZeros64 (bv 64 (g 0)))
  | "OnesCount8" => one (OnesCount8 (bv 8 (g 0))) | "OnesCount16" => one (OnesCount16 (bv 16 (g 0)))
  | "OnesCount32" => one (OnesCount32 (bv 32 (g 0))) | "OnesCount64" => one (OnesCount64 (bv 64 (g 0)))
  | "Reverse8" => one (Reverse8 (bv 8 (g 0))) | "Reverse16" => one (Reverse16 (bv 16 (g 0)))
  | "Reverse32" => one (Reverse32 (bv 32 (g 0))) | "Reverse64" => one (Reverse64 (bv 64 (g 0)))
  | "ReverseBytes16" => one (ReverseBytes16 (bv 16 (g 0)))
  | "ReverseBytes32" => one (ReverseBytes32 (bv 32 (g 0)))
  | "ReverseBytes64" => one (ReverseBytes64 (bv 64 (g 0)))
  | "RotateLeft8" => one (RotateLeft8 (bv 8 (g 0)) (bv 64 (g 1)))
  | "RotateLeft16" => one (RotateLeft16 (bv 16 (g 0)) (bv 64 (g 1)))
  | "RotateLeft32" => one (RotateLeft32 (bv 32 (g 0)) (bv 64 (g 1)))
  | "RotateLeft64" => one (RotateLeft64 (bv 64 (g 0)) (bv 64 (g 1)))
  | "Add32" => two (Add32 (bv 32 (g 0)) (bv 32 (g 1)) (bv 32 (g 2)))
  | "Add64" => two (Add64 (bv 64 (g 0)) (bv 64 (g 1)) (bv 64 (g 2)))
  | "Sub32" => two (Sub32 (bv 32 (g 0)) (bv 32 (g 1)) (bv 32 (g 2)))
  | "Sub64" => two (Sub64 (bv 64 (g 0)) (bv 64 (g 1)) (bv 64 (g 2)))
  | "Mul32" => two (Mul32 (bv 32 (g 0)) (bv 32 (g 1)))
  | "Mul64" => two (Mul64 (bv 64 (g 0)) (bv 64 (g 1)))
  | "Div32" => ex (Div32 (bv 32 (g 0)) (bv 32 (g 1)) (bv 32 (g 2)))
  | "Div64" => ex (Div64 (bv 64 (g 0)) (bv 64 (g 1)) (bv 64 (g 2)))
  | "Rem64" => ex1 (Rem64 (bv 64 (g 0)) (bv 64 (g 1)) (bv 64 (g 2)))
  | _ => none

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: checkvectors <vectors.json>"; return 2
  let txt ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse txt)
  let arr ← IO.ofExcept (json.getArr?)
  let mut checked := 0
  let mut skipped : Std.HashMap String Nat := {}
  let mut failures := 0
  let mut perFn : Std.HashMap String Nat := {}
  for j in arr do
    let v ← IO.ofExcept (parseVec j)
    match eval v with
    | none => skipped := skipped.insert v.fn (skipped.getD v.fn 0 + 1)
    | some r =>
      checked := checked + 1
      perFn := perFn.insert v.fn (perFn.getD v.fn 0 + 1)
      let expected : Except String (Array Nat) :=
        match v.panic, v.out with
        | some p, _ => .error p
        | none, some o => .ok o
        | none, none => .error "<malformed>"
      let same := match r, expected with
        | .ok a, .ok b => a == b
        | .error a, .error b => a == b
        | _, _ => false
      if !same then
        failures := failures + 1
        if failures ≤ 20 then
          IO.eprintln s!"MISMATCH {v.fn} in={v.inp} go={repr expected} lean={repr r}"
  IO.println s!"checked {checked} vectors over {perFn.size} functions; {failures} mismatches"
  for (fn, n) in perFn.toList do IO.println s!"  {fn}: {n}"
  if !skipped.isEmpty then
    IO.println s!"skipped (no Lean model): {skipped.toList}"
  return (if failures == 0 then 0 else 1)
