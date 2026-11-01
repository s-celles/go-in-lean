import GoInLean.Semantics.Int
/-!
# Go slices with a backing array (aliasing-aware model)

Spec: "Slice types": a slice is a descriptor `(pointer, length, capacity)`
for a contiguous segment of an underlying array; `s[low:high]` and
`s[low:high:max]` share the array; `append` writes in place when the
capacity suffices and otherwise allocates a new array; `copy` has
memmove semantics ("overlapping slices" allowed).

The model is a small heap of arrays plus descriptors. All operations run in
`M α := StateT (Heap α) (Except Panic)` so that transliterated Go reads as
`do` blocks. Indices are Go `int`s modelled as `Int` (negative → panic).

Deliberate simplifications (documented in `docs/semantic-boundary.md`):
* allocation on growth gives capacity exactly `len + extra` (Go's
  `growslice` rounds up to a size class; capacity values are never part of
  the specifications proved here, only contents are);
* the zero value of the element type is `default` ([Inhabited α]);
* `overlaps` is index-range intersection within one array (Go compares
  addresses; for element size 0 Go returns false, which cannot arise here).
-/
namespace Go.Mem

abbrev ArrId := Nat

structure Heap (α : Type) where
  arrays : Array (Array α)
  deriving Repr

structure Slice where
  arr : ArrId
  off : Nat
  len : Nat
  cap : Nat
  deriving Repr, DecidableEq, BEq

abbrev M (α : Type) (β : Type) := StateT (Heap α) (Except Panic) β

variable {α : Type} [Inhabited α]

def panic' {β : Type} (p : Panic) : M α β := fun _ => .error p

/-- `len(s)`, `cap(s)` as Go `int`s. -/
def len (s : Slice) : Int := s.len
def cap (s : Slice) : Int := s.cap

def readArr (a : ArrId) : M α (Array α) := do
  let h ← get
  match h.arrays[a]? with
  | some arr => pure arr
  | none => panic' .indexOutOfRange
def writeArr (a : ArrId) (arr : Array α) : M α Unit :=
  modify fun h => { arrays := h.arrays.set! a arr }

/-- `s[i]` (read). -/
def index (s : Slice) (i : Int) : M α α := do
  if i < 0 ∨ i ≥ s.len then panic' .indexOutOfRange
  let arr ← readArr s.arr
  match arr[s.off + i.toNat]? with
  | some x => pure x
  | none => panic' .indexOutOfRange

/-- `s[i] = x`. -/
def store (s : Slice) (i : Int) (x : α) : M α Unit := do
  if i < 0 ∨ i ≥ s.len then panic' .indexOutOfRange
  let arr ← readArr s.arr
  if s.off + i.toNat ≥ arr.size then panic' .indexOutOfRange
  writeArr s.arr (arr.set! (s.off + i.toNat) x)

/-- `s[i:j]` (two-index slice expression): `0 ≤ i ≤ j ≤ cap(s)`. -/
def slice (s : Slice) (i j : Int) : M α Slice := do
  if i < 0 ∨ j < i ∨ j > s.cap then panic' .indexOutOfRange
  pure { arr := s.arr, off := s.off + i.toNat, len := (j - i).toNat, cap := s.cap - i.toNat }
/-- `s[i:j:k]` (full slice expression): `0 ≤ i ≤ j ≤ k ≤ cap(s)`. -/
def slice3 (s : Slice) (i j k : Int) : M α Slice := do
  if i < 0 ∨ j < i ∨ k < j ∨ k > s.cap then panic' .indexOutOfRange
  pure { arr := s.arr, off := s.off + i.toNat, len := (j - i).toNat, cap := (k - i).toNat }
/-- `s[i:]` -/
def sliceFrom (s : Slice) (i : Int) : M α Slice := slice s i s.len
/-- `s[:j]` -/
def sliceTo (s : Slice) (j : Int) : M α Slice := slice s 0 j

/-- The elements `s[0], …, s[len-1]` as a list (a read, no Go counterpart). -/
def toList (s : Slice) : M α (List α) := do
  let arr ← readArr s.arr
  if s.off + s.len > arr.size then panic' .indexOutOfRange
  pure ((List.range s.len).map fun k => arr[s.off + k]!)

/-- Write `xs` at `s[0…]`; caller guarantees `xs.length ≤ len`. -/
def writeList (s : Slice) (xs : List α) : M α Unit := do
  let arr ← readArr s.arr
  let mut a := arr
  for k in [0:xs.length] do
    a := a.set! (s.off + k) xs[k]!
  writeArr s.arr a

/-- `copy(dst, src)`: memmove semantics, returns the number of elements copied. -/
def copy (dst src : Slice) : M α Int := do
  let n := min dst.len src.len
  let xs ← toList { src with len := n, cap := n }
  writeList { dst with len := n } xs
  pure n

/-- `clear(s)`: zero the elements. -/
def clear (s : Slice) : M α Unit := writeList s (List.replicate s.len default)

/-- Allocate a fresh array holding `xs` and return a slice over it. -/
def alloc (xs : List α) : M α Slice := do
  let h ← get
  let id := h.arrays.size
  set { arrays := h.arrays.push xs.toArray : Heap α }
  pure { arr := id, off := 0, len := xs.length, cap := xs.length }

/-- `make([]T, n)` -/
def make (n : Int) : M α Slice := do
  if n < 0 then panic' (.message "makeslice: len out of range")
  alloc (List.replicate n.toNat default)

/-- `append(s, xs...)` with `xs` already read (values captured before any write, as Go does
when the arguments are evaluated). In place when `len + |xs| ≤ cap`, else a new array of
capacity exactly `len + |xs|` (see header). -/
def appendVals (s : Slice) (xs : List α) : M α Slice := do
  let n := s.len + xs.length
  if n ≤ s.cap then
    let tail : Slice := { arr := s.arr, off := s.off + s.len, len := xs.length, cap := s.cap - s.len }
    writeList tail xs
    pure { s with len := n }
  else
    let old ← toList s
    alloc (old ++ xs)

/-- `append(s, v...)` with a slice argument (possibly aliasing `s`). -/
def appendSlice (s v : Slice) : M α Slice := do
  let xs ← toList v
  appendVals s xs

/-- `overlaps(a, b)` from slices.go:453-466, for a non-zero element size. -/
def overlaps (a b : Slice) : Bool :=
  a.len ≠ 0 && b.len ≠ 0 && a.arr == b.arr &&
  a.off ≤ b.off + b.len - 1 && b.off ≤ a.off + a.len - 1

/-- `startIdx(haystack, needle)` from slices.go:469-479: the index in `haystack` of
`&needle[0]`; Go panics "needle not found" otherwise. -/
def startIdx (haystack needle : Slice) : M α Int := do
  if needle.len = 0 then panic' .indexOutOfRange
  if needle.arr = haystack.arr ∧ haystack.off ≤ needle.off ∧ needle.off < haystack.off + haystack.len then
    pure (needle.off - haystack.off : Nat)
  else panic' (.message "needle not found")

/-- Run a computation on a heap; `Except` carries the panic. -/
def run {β : Type} (m : M α β) (h : Heap α) : Except Panic (β × Heap α) := m h

end Go.Mem
