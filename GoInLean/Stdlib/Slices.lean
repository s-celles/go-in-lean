import GoInLean.Semantics.Int
import GoInLean.Stdlib.Bits
/-!
# Model of selected `slices` / `sort` functions (go1.25.5)

Slices are modelled as `List α` (length only, no capacity, no aliasing):
this covers the *value* semantics of the pure functions below but not the
in-place/aliasing behaviour of `Insert`, `Replace`, `Delete` (which also
clear the tail), so those are **not** modelled here (see
`docs/research-report.md`). Comments give the Go source lines.
-/
namespace Go.Slices
open Go

/-- `sort.Search`'s midpoint computation `int(uint(i+j) >> 1)` (search.go:63),
used identically by `slices.BinarySearch` (sort.go:133). Both `i`, `j` are Go `int`s. -/
def midpoint (i j : int) : int := Go.convU 64 ((Go.convU 64 (i + j)) >>> 1)

/-- `slices.Repeat`/`strings.Repeat`/`bytes.Repeat` overflow guard (slices.go:519-522):
`hi, lo := bits.Mul(uint(len(x)), uint(count)); if hi > 0 || lo > maxInt { panic }`. -/
def repeatOverflows (len count : uint) : Bool :=
  let (hi, lo) := Go.Bits.Mul len count
  hi > 0 || lo > Go.maxInt

/-- `slices.Compact` (slices.go:369-388) as a functional program on lists: the
in-place loop keeps the first element of every run of equal adjacent elements.
`clear(s[k:])` is unobservable in the list model. -/
def Compact {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | [a] => [a]
  | a :: b :: rest => if a = b then Compact (b :: rest) else a :: Compact (b :: rest)

/-- `slices.Index` (slices.go:96-103): `for i := range s { if v == s[i] { return i } }; return -1`,
written as a recursion carrying the current index. -/
def indexFrom {α : Type} [DecidableEq α] (v : α) : List α → Nat → Int
  | [], _ => -1
  | a :: t, i => if a = v then i else indexFrom v t (i + 1)
def Index {α : Type} [DecidableEq α] (s : List α) (v : α) : Int := indexFrom v s 0

/-- `slices.Contains` (slices.go:117-119). -/
def Contains {α : Type} [DecidableEq α] (s : List α) (v : α) : Bool := Index s v ≥ 0

/-- `sort.Search` (search.go:58-74), with `f` monotone from the doc comment
("f(i) == true implies f(i+1) == true"). Written with the loop as a
well-founded recursion on `j - i`; `n` is a Go `int` assumed `0 ≤ n`. -/
def searchLoop (f : Nat → Bool) (i j : Nat) : Nat :=
  if h : i < j then
    let m := (i + j) / 2
    if f m then searchLoop f i m else searchLoop f (m + 1) j
  else i
termination_by j - i
decreasing_by all_goals omega

def Search (n : Nat) (f : Nat → Bool) : Nat := searchLoop f 0 n

end Go.Slices
