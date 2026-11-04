import Lean.Data.Json
import GoInLean.Semantics.Int
import GoInLean.Semantics.Float64
import GoInLean.Semantics.Float32

/-!
# The Lean oracle for SIMD expression chains (milestone J3, integers and masks)

`lake exe oracle-simd exprs.json` evaluates every SIMD chain record of the
JSON file against Go's documented `simd` package semantics for the integer
and mask types, at the 128-bit vector size every configuration can run
(the campaign forces GODEBUG=simd=128), and prints one line per record:

* `expr <i>: 0x<hex>` - the FNV-1a checksum of the first min(4, 128/w)
  lanes, zero-extended, exactly the line the Go program built by
  `scripts/simd_oracle.py` prints.

The value model: a vector is a list of lanes stored zero-extended in
`BitVec 64` (only the low `w` bits matter); each operation truncates its
lanes to `w`, computes, and pads back. Masks are vectors whose lanes are
0 or 1. Where the package documents architecture-dependent behaviour
(amd64 float Min/Max, the wasm and emulated unfused MulAdd of
golang/go#80355) the oracle follows the *specification* - that is the
point: it sees the classes where every implementation is wrong together.
This first step covers the integer and mask operations; floats come with
the modelled FMA later.

Records: `{"e", "ops"}` where ops is RPN over vectors:
`vpush {w,s,v:[..]}`, `vbcast {w,s,v}`, `vbin {op}`, `vshift {op,c}`,
`vrot {c}`, `vcmp {op}`, `mbin {op}`, `mun {op}`, `vsel`, `vmasked`,
`vtomask`, `vfrommask {w}`.
-/
open Lean Go

/-- A vector value: lanes zero-extended into `BitVec 64`; a mask is the same
shape with 0/1 lanes. -/
structure VS where
  w : Nat
  s : Bool
  vals : List (BitVec 64)

def bitw (v : Nat) : BitVec 64 := BitVec.ofNat 64 v

/-- The lane value at width `w` (truncate to the low bits). -/
def lane (w : Nat) (x : BitVec 64) : BitVec w := x.setWidth w

/-- A computed lane, padded back to the uniform representation. -/
def pad {w : Nat} (x : BitVec w) : BitVec 64 := x.setWidth 64

def evalBin (op : String) (s : Bool) {w : Nat} (a b : BitVec w) : BitVec w :=
  match op with
  | "fadd" =>
      if h : w = 64 then
        let a' : BitVec 64 := by rw [← h]; exact a
        let b' : BitVec 64 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float64.addBits a' b')
      else if h : w = 32 then
        let a' : BitVec 32 := by rw [← h]; exact a
        let b' : BitVec 32 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float32.addBits a' b')
      else a
  | "fsub" =>
      if h : w = 64 then
        let a' : BitVec 64 := by rw [← h]; exact a
        let b' : BitVec 64 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float64.subBits a' b')
      else if h : w = 32 then
        let a' : BitVec 32 := by rw [← h]; exact a
        let b' : BitVec 32 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float32.subBits a' b')
      else a
  | "fmul" =>
      if h : w = 64 then
        let a' : BitVec 64 := by rw [← h]; exact a
        let b' : BitVec 64 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float64.mulBits a' b')
      else if h : w = 32 then
        let a' : BitVec 32 := by rw [← h]; exact a
        let b' : BitVec 32 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float32.mulBits a' b')
      else a
  | "fdiv" =>
      if h : w = 64 then
        let a' : BitVec 64 := by rw [← h]; exact a
        let b' : BitVec 64 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float64.divBits a' b')
      else if h : w = 32 then
        let a' : BitVec 32 := by rw [← h]; exact a
        let b' : BitVec 32 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float32.divBits a' b')
      else a
  | "fmin" =>
      if h : w = 64 then
        let a' : BitVec 64 := by rw [← h]; exact a
        let b' : BitVec 64 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float64.minBits a' b')
      else if h : w = 32 then
        let a' : BitVec 32 := by rw [← h]; exact a
        let b' : BitVec 32 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float32.minBits a' b')
      else a
  | "fmax" =>
      if h : w = 64 then
        let a' : BitVec 64 := by rw [← h]; exact a
        let b' : BitVec 64 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float64.maxBits a' b')
      else if h : w = 32 then
        let a' : BitVec 32 := by rw [← h]; exact a
        let b' : BitVec 32 := by rw [← h]; exact b
        (by rw [h]; exact Go.Float32.maxBits a' b')
      else a
  | "addsat" =>
      -- AddSaturated: clamp to the (un)signed range of the width.
      -- BitVec.toInt is the two's-complement value; toNat is unsigned.
      if s then
        let r := a.toInt + b.toInt
        let lo : Int := -(2 ^ (w - 1))
        let hi : Int := 2 ^ (w - 1) - 1
        BitVec.ofInt w (if r < lo then lo else if r > hi then hi else r)
      else
        let r := a.toNat + b.toNat
        BitVec.ofNat w (if r > 2 ^ w - 1 then 2 ^ w - 1 else r)
  | "subsat" =>
      -- SubSaturated: clamp to the (un)signed range of the width
      if s then
        let r := a.toInt - b.toInt
        let lo : Int := -(2 ^ (w - 1))
        let hi : Int := 2 ^ (w - 1) - 1
        BitVec.ofInt w (if r < lo then lo else if r > hi then hi else r)
      else
        let r := a.toNat - b.toNat
        BitVec.ofNat w (if r < 0 then 0 else r)
  | "avg" =>
      -- Average: (x + y + 1) / 2, rounded toward +Inf (unsigned only)
      BitVec.ofNat w ((a.toNat + b.toNat + 1) / 2)
  | "add" => a + b
  | "sub" => a - b
  | "mul" => a * b
  | "and" => a &&& b
  | "or"  => a ||| b
  | "xor" => a ^^^ b
  | "andnot" => a &&& ~~~b
  | "min" => if (if s then a.slt b else a < b) then a else b
  | "max" => if (if s then b.slt a else b < a) then a else b
  | _ => a

def evalCmp (op : String) (s : Bool) {w : Nat} (a b : BitVec w) : Bool :=
  match op with
  | "feq" =>
      if h : w = 64 then
        let x' : BitVec 64 := by rw [← h]; exact a
        let y' : BitVec 64 := by rw [← h]; exact b
        Go.Float64.eqBits x' y'
      else if h : w = 32 then
        let x' : BitVec 32 := by rw [← h]; exact a
        let y' : BitVec 32 := by rw [← h]; exact b
        Go.Float32.eqBits x' y'
      else false
  | "fne" =>
      if h : w = 64 then
        let x' : BitVec 64 := by rw [← h]; exact a
        let y' : BitVec 64 := by rw [← h]; exact b
        !Go.Float64.eqBits x' y'
      else if h : w = 32 then
        let x' : BitVec 32 := by rw [← h]; exact a
        let y' : BitVec 32 := by rw [← h]; exact b
        !Go.Float32.eqBits x' y'
      else false
  | "flt" =>
      if h : w = 64 then
        let x' : BitVec 64 := by rw [← h]; exact a
        let y' : BitVec 64 := by rw [← h]; exact b
        Go.Float64.ltBits x' y'
      else if h : w = 32 then
        let x' : BitVec 32 := by rw [← h]; exact a
        let y' : BitVec 32 := by rw [← h]; exact b
        Go.Float32.ltBits x' y'
      else false
  | "fle" =>
      if h : w = 64 then
        let x' : BitVec 64 := by rw [← h]; exact a
        let y' : BitVec 64 := by rw [← h]; exact b
        Go.Float64.leBits x' y'
      else if h : w = 32 then
        let x' : BitVec 32 := by rw [← h]; exact a
        let y' : BitVec 32 := by rw [← h]; exact b
        Go.Float32.leBits x' y'
      else false
  | "fgt" =>
      if h : w = 64 then
        let x' : BitVec 64 := by rw [← h]; exact b
        let y' : BitVec 64 := by rw [← h]; exact a
        Go.Float64.ltBits x' y'
      else if h : w = 32 then
        let x' : BitVec 32 := by rw [← h]; exact b
        let y' : BitVec 32 := by rw [← h]; exact a
        Go.Float32.ltBits x' y'
      else false
  | "fge" =>
      if h : w = 64 then
        let x' : BitVec 64 := by rw [← h]; exact b
        let y' : BitVec 64 := by rw [← h]; exact a
        Go.Float64.leBits x' y'
      else if h : w = 32 then
        let x' : BitVec 32 := by rw [← h]; exact b
        let y' : BitVec 32 := by rw [← h]; exact a
        Go.Float32.leBits x' y'
      else false
  | "eq" => a == b
  | "ne" => a != b
  | "lt" => if s then a.slt b else a < b
  | "le" => if s then a.sle b else a ≤ b
  | "gt" => if s then b.slt a else b < a
  | "ge" => if s then b.sle a else b ≤ a
  | _ => false

/-- One RPN step over the vector stack. -/
def stepS (st : Array VS) (j : Json) : Except String (Array VS) := do
  let k ← j.getObjValAs? String "k"
  let pop (st : Array VS) : Except String (Array VS × VS) :=
    match st.back? with
    | none => throw "stack underflow"
    | some v => return (st.pop, v)
  match k with
  | "vpush" =>
      let w ← j.getObjValAs? Nat "w"
      let s ← j.getObjValAs? Bool "s"
      let arr ← j.getObjValAs? (Array Nat) "v"
      return st.push ⟨w, s, arr.toList.map bitw⟩
  | "vbcast" =>
      let w ← j.getObjValAs? Nat "w"
      let s ← j.getObjValAs? Bool "s"
      let v ← j.getObjValAs? Nat "v"
      let lanes := 128 / w
      return st.push ⟨w, s, (List.range lanes).map (fun _ => bitw v)⟩
  | "vbin" =>
      let op ← j.getObjValAs? String "op"
      let (st, b) ← pop st
      let (st, a) ← pop st
      if a.w != b.w || a.s != b.s then throw "vbin shape mismatch"
      let vals := (a.vals.zip b.vals).map (fun (x, y) =>
        pad (evalBin op a.s (lane a.w x) (lane a.w y)))
      return st.push ⟨a.w, a.s, vals⟩
  | "vshift" =>
      let op ← j.getObjValAs? String "op"
      let c ← j.getObjValAs? Nat "c"
      let (st, a) ← pop st
      -- ShiftAllLeft/Right: a count >= w gives 0 or the sign fill
      let n := min c a.w
      let vals := a.vals.map (fun x =>
        let v := lane a.w x
        pad (if op == "shl" then v <<< n
             else if a.s then v.sshiftRight n else v >>> n))
      return st.push ⟨a.w, a.s, vals⟩
  | "vrot" =>
      let c ← j.getObjValAs? Nat "c"
      let dir := match j.getObjValAs? String "op" with
        | .ok d => d
        | .error _ => "rotl"
      let (st, a) ← pop st
      -- bits.RotateLeftN/RotateRightN: rotate by c mod w
      let n := c % a.w
      let vals := a.vals.map (fun x =>
        let v := lane a.w x
        pad (if dir == "rotr"
             then (v >>> n) ||| (v <<< (a.w - n))
             else (v <<< n) ||| (v >>> (a.w - n))))
      return st.push ⟨a.w, a.s, vals⟩
  | "vcmp" =>
      let op ← j.getObjValAs? String "op"
      let (st, b) ← pop st
      let (st, a) ← pop st
      if a.w != b.w || a.s != b.s then throw "vcmp shape mismatch"
      let vals := (a.vals.zip b.vals).map (fun (x, y) =>
        bitw (if evalCmp op a.s (lane a.w x) (lane a.w y) then 1 else 0))
      return st.push ⟨a.w, false, vals⟩
  | "mbin" =>
      let op ← j.getObjValAs? String "op"
      let (st, b) ← pop st
      let (st, a) ← pop st
      if a.w != b.w then throw "mbin shape mismatch"
      let vals := (a.vals.zip b.vals).map (fun (x, y) =>
        bitw (if match op with
          | "and" => x.toNat == 1 && y.toNat == 1
          | "or"  => x.toNat == 1 || y.toNat == 1
          | "xor" => (x.toNat == 1) != (y.toNat == 1)
          | "eq"  => x == y
          | _ => false then 1 else 0))
      return st.push ⟨a.w, false, vals⟩
  | "mun" =>
      let op ← j.getObjValAs? String "op"
      let (st, a) ← pop st
      if op != "not" then throw "mun op"
      let vals := a.vals.map (fun x => bitw (if x.toNat == 1 then 0 else 1))
      return st.push ⟨a.w, false, vals⟩
  | "vsel" =>
      -- IfElse(mask, x, y): pops y, x, mask
      let (st, y) ← pop st
      let (st, x) ← pop st
      let (st, m) ← pop st
      if x.w != y.w || x.s != y.s || m.w != x.w then throw "vsel shape mismatch"
      let vals := (x.vals.zip (y.vals.zip m.vals)).map (fun (xv, (yv, mv)) =>
        if mv.toNat == 1 then xv else yv)
      return st.push ⟨x.w, x.s, vals⟩
  | "vmasked" =>
      -- Masked(mask): x where the mask is true, 0 elsewhere
      -- (the generator pushes the mask first, then x; x is on top)
      let (st, x) ← pop st
      let (st, m) ← pop st
      if m.w != x.w then throw "vmasked shape mismatch"
      let vals := (x.vals.zip m.vals).map (fun (xv, mv) =>
        if mv.toNat == 1 then xv else 0)
      return st.push ⟨x.w, x.s, vals⟩
  | "vtomask" =>
      let (st, a) ← pop st
      let vals := a.vals.map (fun x => bitw (if x.toNat != 0 then 1 else 0))
      return st.push ⟨a.w, false, vals⟩
  | "vfrommask" =>
      let w ← j.getObjValAs? Nat "w"
      let (st, m) ← pop st
      let vals := m.vals.map (fun x =>
        if x.toNat == 1 then pad (~~~(0 : BitVec w)) else 0)
      return st.push ⟨w, true, vals⟩
  | "vfun" =>
      -- unary float ops on bit patterns: abs clears the sign, neg flips it
      let op ← j.getObjValAs? String "op"
      let (st, a) ← pop st
      -- the sign bit sits at the lane width: bit 63 for float64 lanes,
      -- bit 31 for float32 lanes stored zero-extended
      let smask : BitVec 64 := if a.w == 64 then 0x7FFFFFFFFFFFFFFF else 0x7FFFFFFF
      let sbit : BitVec 64 := if a.w == 64 then 0x8000000000000000 else 0x80000000
      let vals := a.vals.map (fun x =>
        match op with
        | "fabs" => x &&& smask
        | "fneg" => x ^^^ sbit
        | "fsqrt" =>
            if a.w == 64 then Go.Float64.sqrtBits x
            else pad (Go.Float32.sqrtBits (lane 32 x))
        | "onescount" => pad (lane a.w x).cpop
        | _ => x)
      return st.push ⟨a.w, a.s, vals⟩
  | "vreduce" =>
      -- ReduceSum. The floats use repeated pairwise summation, exactly as
      -- documented: ((x[0]+x[1]) + (x[2]+x[3])) + ...; the ints wrap at the
      -- lane width. Only the real 128/w lanes take part (a table push
      -- carries more lanes; the Go side reduces the loaded vector).
      let op ← j.getObjValAs? String "op"
      let (st, a) ← pop st
      if op == "f" then
        if a.w == 32 then
          let ls := ((a.vals.take 4).map (fun x => lane 32 x))
          match ls with
          | [x0, x1, x2, x3] =>
              let r := Go.Float32.addBits (Go.Float32.addBits x0 x1) (Go.Float32.addBits x2 x3)
              return st.push ⟨32, true, [pad r]⟩
          | _ => throw "vreduce f32 lane count"
        else if a.w == 64 then
          match (a.vals.take 2).map (fun x => lane 64 x) with
          | [x0, x1] =>
              let r := Go.Float64.addBits x0 x1
              return st.push ⟨64, true, [pad r]⟩
          | _ => throw "vreduce f64 lane count"
        else throw "vreduce float width"
      else
        let nl := 128 / a.w
        let total := ((a.vals.take nl).map (fun x => lane a.w x)).foldl
          (fun acc x => acc + x) (BitVec.ofNat a.w 0)
        return st.push ⟨a.w, a.s, [pad total]⟩
  | "vfma" =>
      -- MulAdd per the spec: fused, single rounding
      let (st, z) ← pop st
      let (st, y) ← pop st
      let (st, x) ← pop st
      if x.w != y.w || x.w != z.w then throw "vfma shape mismatch"
      if x.w == 64 then
        let vals := ((x.vals.zip (y.vals.zip z.vals))).map (fun (xv, (yv, zv)) =>
          Go.Float64.fmaBits xv yv zv)
        return st.push ⟨x.w, x.s, vals⟩
      else if x.w == 32 then
        let vals := ((x.vals.zip (y.vals.zip z.vals))).map (fun (xv, (yv, zv)) =>
          pad (Go.Float32.fmaBits (lane 32 xv) (lane 32 yv) (lane 32 zv)))
        return st.push ⟨x.w, x.s, vals⟩
      else throw "vfma width"
  | k => throw s!"unknown vector op {k}"

def evalOpsS (ops : Array Json) : Except String VS := do
  let mut st : Array VS := #[]
  for o in ops do
    st ← stepS st o
  match st with
  | #[v] => return v
  | _ => throw "stack must hold exactly one vector"

def fnv (h : Nat) (n : Nat) : Nat := (h ^^^ n) * 1099511628211 % (2 ^ 64)

-- NaN payloads are unspecified (IEEE and the package docs): the model only
-- ever produces the canonical nanBits, and the Go program canonicalizes its
-- NaN lanes to the same pattern before checksumming, so payload noise from
-- the hardware never reaches the comparison.

def checksum (v : VS) : String :=
  -- FNV-1a over the first min(4, 128/w) lanes, zero-extended, exactly the
  -- checksum the Go program prints
  let nlane := min 4 (128 / v.w)
  let h := (v.vals.take nlane).foldl (fun h x => fnv h x.toNat) 1469598103934665603
  s!"0x{String.ofList (Nat.toDigits 16 h)}"

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: oracle-simd <exprs.json>"; return 2
  let txt ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse txt)
  let arr ← IO.ofExcept (json.getArr?)
  let mut bad := 0
  for j in arr do
    let e ← IO.ofExcept (j.getObjValAs? Nat "e")
    let ops ← IO.ofExcept (j.getObjValAs? (Array Json) "ops")
    match evalOpsS ops with
    | .ok v => IO.println s!"expr {e}: {checksum v}"
    | .error m => IO.eprintln s!"bad record e={e}: {m}"; bad := bad + 1
  if bad > 0 then return 1
  return 0
