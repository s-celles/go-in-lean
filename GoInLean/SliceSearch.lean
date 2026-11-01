import GoInLean.Stdlib.SlicesArr
/-!
# Bounded exhaustive search: slices model vs specification

`lake exe slicesearch [N]` enumerates every configuration of one backing
array of size `N` (default 6) holding distinct values `1..N`, a slice
`s = a[off:off+len:off+cap]`, an argument slice `v` either aliasing the same
array (`a[x:y]`) or living in a second array, and all index arguments. For
each configuration it runs the Lean models of `Insert`, `Delete`, `Replace`
and compares the resulting contents with the documented specification
(`s[:i] ++ v ++ s[i:]`, `s[:i] ++ s[j:]` plus cleared tail,
`s[:i] ++ v ++ s[j:]`). Mismatches are printed as JSON lines (stage E of the
pipeline: counterexample exploration by finite-domain search). Exit status 1
on any mismatch. This is a *search*, not a proof; it runs compiled code.
-/
open Go Go.Mem Go.SlicesArr

structure Config where
  n : Nat
  soff : Nat
  slen : Nat
  scap : Nat
  valias : Bool     -- v in the same array?
  voff : Nat
  vlen : Nat
  i : Int
  j : Int
  deriving Repr

def heapFor (c : Config) : Heap Nat :=
  { arrays := #[(List.range c.n).map (· + 1) |>.toArray, (List.range c.n).map (· + 101) |>.toArray] }
def sliceS (c : Config) : Slice := { arr := 0, off := c.soff, len := c.slen, cap := c.scap }
def sliceV (c : Config) : Slice :=
  { arr := if c.valias then 0 else 1, off := c.voff, len := c.vlen, cap := c.vlen }

def jsonOf (c : Config) (fn : String) (got want : String) : String :=
  s!"\{\"fn\": \"{fn}\", \"n\": {c.n}, \"s\": [{c.soff}, {c.slen}, {c.scap}], \"v_alias\": {c.valias}, \"v\": [{c.voff}, {c.vlen}], \"i\": {c.i}, \"j\": {c.j}, \"got\": {got}, \"want\": {want}}"

/-- Run `m` and return the contents of the result slice (or the panic name). -/
def contents (h : Heap Nat) (m : M Nat Slice) : String :=
  match (do let r ← m; toList r : M Nat (List Nat)) h with
  | .ok (xs, _) => toString xs
  | .error p => s!"\"panic:{repr p}\""

def specList (xs : List Nat) : String := toString xs

def checkInsert (c : Config) : Option String := Id.run do
  let h := heapFor c
  let s := sliceS c; let v := sliceV c
  let s0 := (toList s h).toOption.map (·.1) |>.getD []
  let v0 := (toList v h).toOption.map (·.1) |>.getD []
  let want := s0.take c.i.toNat ++ v0 ++ s0.drop c.i.toNat
  let got := contents h (Insert s c.i v)
  if got == specList want then none else some (jsonOf c "Insert" got (specList want))

def checkDelete (c : Config) : Option String := Id.run do
  let h := heapFor c
  let s := sliceS c
  let s0 := (toList s h).toOption.map (·.1) |>.getD []
  let want := s0.take c.i.toNat ++ s0.drop c.j.toNat
  -- also check the tail is cleared: elements s[len(r):oldlen] must be 0 (default)
  let m : M Nat (List Nat × List Nat) := do
    let r ← Delete s c.i c.j
    let xs ← toList r
    let tail ← toList { s with off := s.off + r.len, len := s.len - r.len }
    pure (xs, tail)
  match m h with
  | .ok ((xs, tail), _) =>
    if xs == want ∧ tail.all (· == 0) then none
    else some (jsonOf c "Delete" s!"{xs} tail={tail}" (specList want))
  | .error p => some (jsonOf c "Delete" s!"\"panic:{repr p}\"" (specList want))

def checkReplace (c : Config) : Option String := Id.run do
  let h := heapFor c
  let s := sliceS c; let v := sliceV c
  let s0 := (toList s h).toOption.map (·.1) |>.getD []
  let v0 := (toList v h).toOption.map (·.1) |>.getD []
  let want := s0.take c.i.toNat ++ v0 ++ s0.drop c.j.toNat
  let got := contents h (Replace s c.i c.j v)
  if got == specList want then none else some (jsonOf c "Replace" got (specList want))

def main (args : List String) : IO UInt32 := do
  let n := (args.head? >>= String.toNat?).getD 6
  let mut checked := 0
  let mut bad := 0
  for soff in [0:n+1] do
    for scap in [0:n+1-soff] do
      for slen in [0:scap+1] do
        for valias in [true, false] do
          for voff in [0:n+1] do
            for vlen in [0:n+1-voff] do
              for i in [0:slen+1] do
                -- Insert
                let c : Config := { n, soff, slen, scap, valias, voff, vlen, i := i, j := i }
                checked := checked + 1
                if let some msg := checkInsert c then bad := bad + 1; IO.println msg
                for j in [i:slen+1] do
                  let c := { c with j := j }
                  checked := checked + 1
                  if let some msg := checkReplace c then bad := bad + 1; IO.println msg
                  if valias ∧ voff == 0 ∧ vlen == 0 then
                    checked := checked + 1
                    if let some msg := checkDelete c then bad := bad + 1; IO.println msg
  IO.println s!"slicesearch N={n}: {checked} configurations checked, {bad} mismatches"
  return (if bad == 0 then 0 else 1)
