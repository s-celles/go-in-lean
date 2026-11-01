import GoInLean.Semantics.Slice
/-!
# `slices.Insert`, `Delete`, `Replace`, `Reverse` on the backing-array model (go1.25.5)

Line-by-line transliterations of `src/slices/slices.go` (sha256
`7dc20d436ae48ed87246621877bf160924d800d0d91ef03fb9d5019cdc970e3f`), including
the aliasing case analysis (`overlaps`, `rotateRight`, `startIdx`) introduced
for golang/go#60138 and the `clear` of the tail introduced in Go 1.22
(golang/go#63393). `v ...E` is a slice argument that may alias `s`.
-/
namespace Go.SlicesArr
open Go.Mem

variable {α : Type} [Inhabited α]

/-- `Reverse` (slices.go:481-485). -/
def Reverse (s : Slice) : M α Unit := do
  let mut i : Int := 0
  let mut j : Int := Mem.len s - 1
  while i < j do
    let si ← index s i
    let sj ← index s j
    store s i sj
    store s j si
    i := i + 1
    j := j - 1

/-- `rotateLeft` (slices.go:443-447). -/
def rotateLeft (s : Slice) (r : Int) : M α Unit := do
  Reverse (← sliceTo s r)
  Reverse (← sliceFrom s r)
  Reverse s
/-- `rotateRight` (slices.go:448-450). -/
def rotateRight (s : Slice) (r : Int) : M α Unit := rotateLeft s (Mem.len s - r)

/-- `Insert` (slices.go:135-220). -/
def Insert (s : Slice) (i : Int) (v : Slice) : M α Slice := do
  let _ ← sliceFrom s i  -- bounds check
  let m := Mem.len v
  if m = 0 then return s
  let n := Mem.len s
  if i = n then return (← appendSlice s v)
  if n + m > Mem.cap s then
    let s2 ← appendVals (← sliceTo s i) (List.replicate (n + m - i).toNat default)
    let _ ← copy (← sliceFrom s2 i) v
    let _ ← copy (← sliceFrom s2 (i + m)) (← sliceFrom s i)
    return s2
  let s ← sliceTo s (n + m)
  if !overlaps v (← sliceFrom s (i + m)) then
    let _ ← copy (← sliceFrom s (i + m)) (← sliceFrom s i)
    let _ ← copy (← sliceFrom s i) v
    return s
  let _ ← copy (← sliceFrom s n) v
  rotateRight (← sliceFrom s i) m
  return s

/-- `Delete` (slices.go:222-233). -/
def Delete (s : Slice) (i j : Int) : M α Slice := do
  let _ ← slice3 s i j (Mem.len s)  -- bounds check
  if i = j then return s
  let oldlen := Mem.len s
  let s ← appendSlice (← sliceTo s i) (← sliceFrom s j)
  clear (← slice s (Mem.len s) oldlen)
  return s

/-- `Replace` (slices.go:260-351). -/
def Replace (s : Slice) (i j : Int) (v : Slice) : M α Slice := do
  let _ ← slice s i j  -- bounds check `_ = s[i:j]`
  if i = j then return (← Insert s i v)
  if j = Mem.len s then
    let s2 ← appendSlice (← sliceTo s i) v
    if Mem.len s2 < Mem.len s then
      clear (← sliceFrom s (Mem.len s2))
    return s2
  let tot := Mem.len (← sliceTo s i) + Mem.len v + Mem.len (← sliceFrom s j)
  if tot > Mem.cap s then
    let s2 ← appendVals (← sliceTo s i) (List.replicate (tot - i).toNat default)
    let _ ← copy (← sliceFrom s2 i) v
    let _ ← copy (← sliceFrom s2 (i + Mem.len v)) (← sliceFrom s j)
    return s2
  let r ← sliceTo s tot
  if i + Mem.len v ≤ j then
    let _ ← copy (← sliceFrom r i) v
    let _ ← copy (← sliceFrom r (i + Mem.len v)) (← sliceFrom s j)
    clear (← sliceFrom s tot)
    return r
  if !overlaps (← sliceFrom r (i + Mem.len v)) v then
    let _ ← copy (← sliceFrom r (i + Mem.len v)) (← sliceFrom s j)
    let _ ← copy (← sliceFrom r i) v
    return r
  let y := Mem.len v - (j - i)
  if !overlaps (← slice r i j) v then
    let _ ← copy (← slice r i j) (← sliceFrom v y)
    let _ ← copy (← sliceFrom r (Mem.len s)) (← sliceTo v y)
    rotateRight (← sliceFrom r i) y
    return r
  if !overlaps (← sliceFrom r (Mem.len s)) v then
    let _ ← copy (← sliceFrom r (Mem.len s)) (← sliceTo v y)
    let _ ← copy (← slice r i j) (← sliceFrom v y)
    rotateRight (← sliceFrom r i) y
    return r
  let k ← startIdx v (← sliceFrom s j)
  let _ ← copy (← sliceFrom r i) v
  let _ ← copy (← sliceFrom r (i + Mem.len v)) (← sliceFrom r (i + k))
  return r

end Go.SlicesArr
