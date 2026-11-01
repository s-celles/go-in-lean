import Lean.Data.Json
import GoInLean.Stdlib.SlicesArr
/-!
# Differential check: slices model vs Go on aliasing configurations

`lake exe checkslices build/slices_vectors.json` replays every configuration
recorded by `go/tests/vectors_slices` (real `slices.Insert/Delete/Replace`
of the pinned toolchain) on the Lean model and compares both the returned
contents and the backing array `a` after the call. Panics are compared by
presence only (Go's message vs the model's `Panic` constructor).
-/
open Lean Go Go.Mem Go.SlicesArr

structure Rec where
  fn : String
  n : Nat
  s : Array Nat
  valias : Bool
  v : Array Nat
  i : Int
  j : Int
  result : Array Nat
  arr : Array Nat
  panic : Option String

def parseRec (j : Json) : Except String Rec := do
  pure { fn := ← j.getObjValAs? String "fn", n := ← j.getObjValAs? Nat "n",
         s := ← j.getObjValAs? (Array Nat) "s", valias := ← j.getObjValAs? Bool "v_alias",
         v := ← j.getObjValAs? (Array Nat) "v", i := ← j.getObjValAs? Int "i", j := ← j.getObjValAs? Int "j",
         result := (j.getObjValAs? (Array Nat) "result").toOption.getD #[],
         arr := ← j.getObjValAs? (Array Nat) "arr",
         panic := (j.getObjValAs? String "panic").toOption }

def runModel (r : Rec) : Except Panic (List Nat × Array Nat) :=
  let h : Heap Nat := { arrays := #[(List.range r.n).map (· + 1) |>.toArray, (List.range r.n).map (· + 101) |>.toArray] }
  let s : Slice := { arr := 0, off := r.s[0]!, len := r.s[1]!, cap := r.s[2]! }
  let v : Slice := { arr := if r.valias then 0 else 1, off := r.v[0]!, len := r.v[1]!, cap := r.v[1]! }
  let m : M Nat (List Nat × Array Nat) := do
    let out ← match r.fn with
      | "Insert" => Insert s r.i v
      | "Delete" => Delete s r.i r.j
      | "Replace" => Replace s r.i r.j v
      | _ => panic' (.message "unknown fn")
    let xs ← toList out
    let a ← readArr 0
    pure (xs, a)
  (m h).map (·.1)

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: checkslices <vectors.jsonl>"; return 2
  let txt ← IO.FS.readFile path
  let mut checked := 0
  let mut failures := 0
  let mut perFn : Std.HashMap String Nat := {}
  for line in txt.splitOn "\n" do
    if line.isEmpty then continue
    let j ← IO.ofExcept (Json.parse line)
    let r ← IO.ofExcept (parseRec j)
    checked := checked + 1
    perFn := perFn.insert r.fn (perFn.getD r.fn 0 + 1)
    let ok := match runModel r, r.panic with
      | .ok (xs, a), none => xs.toArray == r.result && a == r.arr
      | .error _, some _ => true
      | _, _ => false
    if !ok then
      failures := failures + 1
      if failures ≤ 20 then
        IO.eprintln s!"MISMATCH {line}\n  lean={repr (runModel r |>.toOption)}"
  IO.println s!"checkslices: {checked} configurations, {failures} mismatches; per fn {perFn.toList}"
  return (if failures == 0 then 0 else 1)
