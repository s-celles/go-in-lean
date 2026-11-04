import Lean.Data.Json
import GoInLean.Semantics.Int
import GoInLean.Stdlib.Bits

/-!
# The Lean oracle for the integer expression fuzzer (milestone J1a)

`lake exe oracle exprs.json` evaluates every expression of the JSON file
against Go's documented integer semantics - the executable model of
`Semantics/Int.lean` (typed conversions, panic-inducing shifts and divisions)
and `Stdlib/Bits.lean` (the math/bits intrinsics) - and prints one line per
record:

* `e=<i> x=<x> y=<y> OK <decimal>` - the value, zero-extended to 64 bits;
* `e=<i> x=<x> y=<y> PANIC <name>` - a run-time panic (divideError,
  negativeShift, other).

Expressions travel in postfix (RPN) form: a record is `{"e", "x", "y", "ops"}`
where `ops` evaluates on a stack - `push` a typed literal, then `un`/`bin`/
`conv`/`bits`/`rot` combine the top of the stack. The generator
`scripts/oracle_bits.py` emits the same expressions as a Go program and
compares the two outputs; a divergence is a candidate miscompilation of the
tested toolchain, triaged like any fuzzer flag. This is the cedar-drt
pattern (`docs/cedar-notes.md`): the model is the in-loop oracle, evaluated
by Lean's compiler, not by the kernel.
-/

open Go Go.Bits Lean

/-- A typed value: `w` bits, signed when `s`, `val` the two's-complement pattern. -/
structure V where
  w : Nat
  s : Bool
  val : BitVec w

/-- One RPN instruction; no children - the stack holds the intermediate values. -/
inductive Op where
  | push (w : Nat) (s : Bool) (v : Nat)
  | un (op : String)
  | bin (op : String)
  | conv (w : Nat) (s : Bool)
  | bits (op : String) (w : Nat)
  | rot (w : Nat)

def perr (m : String) : Except Panic α := .error (Panic.message m)

/-! ## Parsing -/

def parseOp (j : Json) : Except String Op := do
  let k ← j.getObjValAs? String "k"
  match k with
  | "push" =>
    let w ← j.getObjValAs? Nat "w"
    let s ← j.getObjValAs? Bool "s"
    let v ← j.getObjValAs? Nat "v"
    return .push w s v
  | "un" => return .un (← j.getObjValAs? String "op")
  | "bin" => return .bin (← j.getObjValAs? String "op")
  | "conv" =>
    let w ← j.getObjValAs? Nat "w"
    let s ← j.getObjValAs? Bool "s"
    return .conv w s
  | "bits" =>
    let op ← j.getObjValAs? String "op"
    let w ← j.getObjValAs? Nat "w"
    return .bits op w
  | "rot" => return .rot (← j.getObjValAs? Nat "w")
  | k => throw s!"unknown op kind {k}"

structure Rec where
  e : Nat
  x : Nat
  y : Nat
  ops : Array Op

def parseRec (j : Json) : Except String Rec := do
  let e ← j.getObjValAs? Nat "e"
  let x ← j.getObjValAs? Nat "x"
  let y ← j.getObjValAs? Nat "y"
  let arr ← j.getObjValAs? (Array Json) "ops"
  let ops ← arr.mapM parseOp
  return ⟨e, x, y, ops⟩

/-! ## Evaluation -/

/-- The typed comparison used by min/max. -/
def ltV {w : Nat} (s : Bool) (a b : BitVec w) : Bool :=
  if s then a.slt b else a < b

/-- The math/bits intrinsics; the argument is already converted to width `w`, unsigned. -/
def evalBits8 (op : String) (x : BitVec 8) : Except Panic V :=
  match op with
  | "oc" => .ok ⟨64, true, OnesCount8 x⟩
  | "lz" => .ok ⟨64, true, LeadingZeros8 x⟩
  | "tz" => .ok ⟨64, true, TrailingZeros8 x⟩
  | "len" => .ok ⟨64, true, Len8 x⟩
  | "rev" => .ok ⟨8, false, Reverse8 x⟩
  | _ => perr s!"unknown bits op {op}"

def evalBits16 (op : String) (x : BitVec 16) : Except Panic V :=
  match op with
  | "oc" => .ok ⟨64, true, OnesCount16 x⟩
  | "lz" => .ok ⟨64, true, LeadingZeros16 x⟩
  | "tz" => .ok ⟨64, true, TrailingZeros16 x⟩
  | "len" => .ok ⟨64, true, Len16 x⟩
  | "rev" => .ok ⟨16, false, Reverse16 x⟩
  | "rb" => .ok ⟨16, false, ReverseBytes16 x⟩
  | _ => perr s!"unknown bits op {op}"

def evalBits32 (op : String) (x : BitVec 32) : Except Panic V :=
  match op with
  | "oc" => .ok ⟨64, true, OnesCount32 x⟩
  | "lz" => .ok ⟨64, true, LeadingZeros32 x⟩
  | "tz" => .ok ⟨64, true, TrailingZeros32 x⟩
  | "len" => .ok ⟨64, true, Len32 x⟩
  | "rev" => .ok ⟨32, false, Reverse32 x⟩
  | "rb" => .ok ⟨32, false, ReverseBytes32 x⟩
  | _ => perr s!"unknown bits op {op}"

def evalBits64 (op : String) (x : BitVec 64) : Except Panic V :=
  match op with
  | "oc" => .ok ⟨64, true, OnesCount64 x⟩
  | "lz" => .ok ⟨64, true, LeadingZeros64 x⟩
  | "tz" => .ok ⟨64, true, TrailingZeros64 x⟩
  | "len" => .ok ⟨64, true, Len64 x⟩
  | "rev" => .ok ⟨64, false, Reverse64 x⟩
  | "rb" => .ok ⟨64, false, ReverseBytes64 x⟩
  | _ => perr s!"unknown bits op {op}"

/-- `bits.RotateLeftN` at width `w`; the count is a 64-bit signed value (negatives rotate right). -/
def evalRot : (w : Nat) → BitVec w → BitVec 64 → Except Panic V
  | 8, x, k => .ok ⟨8, false, RotateLeft8 x k⟩
  | 16, x, k => .ok ⟨16, false, RotateLeft16 x k⟩
  | 32, x, k => .ok ⟨32, false, RotateLeft32 x k⟩
  | 64, x, k => .ok ⟨64, false, RotateLeft64 x k⟩
  | _, _, _ => perr "rotate width"

/-- One RPN step over the value stack. -/
def step (st : Array V) (o : Op) : Except Panic (Array V) :=
  match o with
  | .push w s v => .ok (st.push ⟨w, s, BitVec.ofNat w v⟩)
  | .un op =>
    match st.back? with
    | none => perr "stack underflow"
    | some ⟨w, s, av⟩ =>
      match op with
      | "neg" => .ok (st.pop.push ⟨w, s, -av⟩)
      | "com" => .ok (st.pop.push ⟨w, s, ~~~av⟩)
      | _ => perr s!"unknown unary {op}"
  | .conv w s =>
    match st.back? with
    | none => perr "stack underflow"
    | some ⟨w0, s0, v0⟩ =>
      let st := st.pop
      if w ≤ w0 then
        .ok (st.push ⟨w, s, v0.setWidth w⟩)
      else if s0 then
        .ok (st.push ⟨w, s, v0.signExtend w⟩)
      else
        .ok (st.push ⟨w, s, v0.setWidth w⟩)
  | .bits op w =>
    match st.back? with
    | none => perr "stack underflow"
    | some va =>
      let st := st.pop
      if h : va.w = w then
        let x : BitVec w := by rw [← h]; exact va.val
        match w, x with
        | 8, x => st.push <$> evalBits8 op x
        | 16, x => st.push <$> evalBits16 op x
        | 32, x => st.push <$> evalBits32 op x
        | 64, x => st.push <$> evalBits64 op x
        | _, _ => perr "bits width"
      else perr "bits width mismatch"
  | .rot w =>
    match st.back? with
    | none => perr "stack underflow"
    | some vk =>
      let st := st.pop
      match st.back? with
      | none => perr "stack underflow"
      | some va =>
        let st := st.pop
        if hk : vk.w = 64 then
          let kk : BitVec 64 := by rw [← hk]; exact vk.val
          if h : va.w = w then
            let x : BitVec w := by rw [← h]; exact va.val
            st.push <$> evalRot w x kk
          else perr "rotate width mismatch"
        else perr "rotate count width"
  | .bin op =>
    match st.back? with
    | none => perr "stack underflow"
    | some vb =>
      let st := st.pop
      match st.back? with
      | none => perr "stack underflow"
      | some va =>
        let st := st.pop
        -- shifts take a count of any width; all other binaries need equal widths
        if op == "shl" || op == "shr" then
          match va, vb with
          | ⟨w, s, av⟩, ⟨_, s', bv⟩ =>
            if s' && bv.msb then .error Panic.negativeShift
            else if op == "shl" then .ok (st.push ⟨w, s, av <<< bv.toNat⟩)
            else if s then .ok (st.push ⟨w, s, av.sshiftRight bv.toNat⟩)
            else .ok (st.push ⟨w, s, av >>> bv.toNat⟩)
        else
          match va, vb with
          | ⟨w, s, av⟩, ⟨w', _, bv⟩ =>
            if h : w = w' then
              let b' : BitVec w := by rw [h]; exact bv
              match op with
              | "add" => .ok (st.push ⟨w, s, av + b'⟩)
              | "sub" => .ok (st.push ⟨w, s, av - b'⟩)
              | "mul" => .ok (st.push ⟨w, s, av * b'⟩)
              | "and" => .ok (st.push ⟨w, s, av &&& b'⟩)
              | "or"  => .ok (st.push ⟨w, s, av ||| b'⟩)
              | "xor" => .ok (st.push ⟨w, s, av ^^^ b'⟩)
              | "min" => .ok (st.push ⟨w, s, if ltV s av b' then av else b'⟩)
              | "max" => .ok (st.push ⟨w, s, if ltV s b' av then av else b'⟩)
              | "div" =>
                if s then
                  match divS av b' with
                  | .ok v => .ok (st.push ⟨w, s, v⟩)
                  | .error p => .error p
                else
                  match divU av b' with
                  | .ok v => .ok (st.push ⟨w, s, v⟩)
                  | .error p => .error p
              | "mod" =>
                if s then
                  match remS av b' with
                  | .ok v => .ok (st.push ⟨w, s, v⟩)
                  | .error p => .error p
                else
                  match remU av b' with
                  | .ok v => .ok (st.push ⟨w, s, v⟩)
                  | .error p => .error p
              | _ => perr s!"unknown binary {op}"
            else perr "bin width mismatch"

def panicStr : Panic → String
  | .divideError => "divideError"
  | .overflowError => "overflowError"
  | .negativeShift => "negativeShift"
  | .indexOutOfRange => "indexOutOfRange"
  | .message _ => "other"

def evalOps (ops : Array Op) : Except Panic V := do
  let mut st : Array V := #[]
  for o in ops do
    st ← step st o
  match st with
  | #[v] => .ok v
  | _ => .error (Panic.message "stack must hold exactly one value")

def evalRec (r : Rec) : String :=
  match evalOps r.ops with
  | .ok v =>
    -- Go prints uint64(result): a signed result sign-extends to 64 bits first
    let v64 := if v.s then v.val.signExtend 64 else v.val.setWidth 64
    s!"e={r.e} x={r.x} y={r.y} OK {v64.toNat}"
  | .error p => s!"e={r.e} x={r.x} y={r.y} PANIC {panicStr p}"

def main (args : List String) : IO UInt32 := do
  let some path := args.head? | IO.eprintln "usage: oracle <exprs.json>"; return 2
  let txt ← IO.FS.readFile path
  let json ← IO.ofExcept (Json.parse txt)
  let arr ← IO.ofExcept (json.getArr?)
  let mut bad := 0
  for j in arr do
    match parseRec j with
    | .error e => IO.eprintln s!"bad record: {e}"; bad := bad + 1
    | .ok r => IO.println (evalRec r)
  if bad > 0 then return 1
  return 0
