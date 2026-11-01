#!/usr/bin/env python3
"""Translate the constant-folding rules of generic.rules into Lean theorems.

Recognised rule shapes (one per line in generic.rules):
    (OpN (ConstN [c]) (ConstN [d])) [&& cond] => (ConstN [goexpr])
    (OpN (ConstN [c])) => (ConstN [goexpr])
    (OpNx64 (ConstN [c]) (Const64 [d])) => (ConstN [goexpr])          shifts
    (TruncAtoB (ConstA [c])) => (ConstB [goexpr]), ZeroExt/SignExt likewise
The Go expression on the right is evaluated by the compiler on *typed*
AuxInts (`auxIntToInt8` … `int8ToAuxInt`, rewritegeneric.go), i.e. with Go's
intN semantics. It is translated to a `BitVec N` expression:
    c+d c-d c*d c&d c|d c^d -c ^c c/d c%d   ->  + - * &&& ||| ^^^ -  ~~~ sdiv srem
    uintN(c)/uintN(d), uintN(c)%uintN(d)    ->  / %                 (unsigned)
    c << uint64(d) ; c >> uint64(d)         ->  <<< d.toNat ; sshiftRight d.toNat
    intN(uintN(c) >> uint64(d))             ->  >>> d.toNat
    intB(c) (narrowing) / intB(uintA(c)) / intB(c) (widening) -> setWidth / setWidth / signExtend
Side condition `d != 0` becomes a hypothesis. Each theorem states
    OpSem.<op> c d = <translated expr>
and is closed by `decide` at width 8 (exhaustive) and `bv_decide` otherwise.
Unrecognised rules are listed in the header comment so that coverage is explicit.
"""
import os, re, subprocess, sys, hashlib

GOROOT = os.environ.get("GOROOT") or subprocess.check_output(["go", "env", "GOROOT"], text=True).strip()
RULES = os.path.join(GOROOT, "src/cmd/compile/internal/ssa/_gen/generic.rules")
OUT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "GoInLean", "Compiler", "GeneratedFolds.lean")

BIN = {"Add": "add", "Sub": "sub", "Mul": "mul", "And": "and", "Or": "or", "Xor": "xor",
       "Div": "div", "Mod": "mod", "Divu": "divu", "Modu": "modu"}
UN = {"Neg": "neg", "Com": "com"}

def lean_expr(expr, width, cvar="c", dvar="d"):
    """Translate a Go AuxInt expression (typed intN) to Lean. Returns (lean, shiftcount_var or None)."""
    e = expr.strip().replace(" ", "")
    w = width
    # shifts
    m = re.fullmatch(rf"int{w}\(uint{w}\({cvar}\)>>uint64\({dvar}\)\)", e)
    if m: return f"{cvar} >>> {dvar}.toNat"
    m = re.fullmatch(rf"{cvar}<<uint64\({dvar}\)", e)
    if m: return f"{cvar} <<< {dvar}.toNat"
    m = re.fullmatch(rf"{cvar}>>uint64\({dvar}\)", e)
    if m: return f"{cvar}.sshiftRight {dvar}.toNat"
    # unsigned div/mod: intN(uintN(c)/uintN(d))
    m = re.fullmatch(rf"int{w}\(uint{w}\({cvar}\)([/%])uint{w}\({dvar}\)\)", e)
    if m: return f"{cvar} {m.group(1)} {dvar}"
    # signed binary
    m = re.fullmatch(rf"{cvar}([-+*&|^/%]){dvar}", e)
    if m:
        op = m.group(1)
        return {"+": f"{cvar} + {dvar}", "-": f"{cvar} - {dvar}", "*": f"{cvar} * {dvar}",
                "&": f"{cvar} &&& {dvar}", "|": f"{cvar} ||| {dvar}", "^": f"{cvar} ^^^ {dvar}",
                "/": f"{cvar}.sdiv {dvar}", "%": f"{cvar}.srem {dvar}"}[op]
    if e == f"-{cvar}": return f"-{cvar}"
    if e == f"^{cvar}": return f"~~~{cvar}"
    return None

def conv_expr(expr, src_w, dst_w, kind):
    e = expr.strip().replace(" ", "")
    if kind == "Trunc" and e == f"int{dst_w}(c)": return f"c.setWidth {dst_w}"
    if kind == "ZeroExt" and e == f"int{dst_w}(uint{src_w}(c))": return f"c.setWidth {dst_w}"
    if kind == "SignExt" and e == f"int{dst_w}(c)": return f"c.signExtend {dst_w}"
    return None

def main():
    src = open(RULES).read()
    sha = hashlib.sha256(src.encode()).hexdigest()
    thms, skipped = [], []
    seen = set()
    for lineno, line in enumerate(src.splitlines(), 1):
        s = line.strip()
        if not s.startswith("(") or "=>" not in s:
            continue
        # conversions
        m = re.fullmatch(r"\((Trunc|ZeroExt|SignExt)(\d+)to(\d+)\s+\(Const(\d+)\s+\[c\]\)\)\s*=>\s*\(Const(\d+)\s+\[(.*)\]\)", s)
        if m:
            kind, a, b, ca, cb, expr = m.groups()
            if ca != a or cb != b: skipped.append((lineno, s)); continue
            le = conv_expr(expr, int(a), int(b), kind)
            if le is None: skipped.append((lineno, s)); continue
            name = f"{kind}{a}to{b}_fold"
            op = {"Trunc": "trunc", "ZeroExt": "zeroExt", "SignExt": "signExt"}[kind]
            thms.append((name, lineno, s, f"(c : BitVec {a})", f"OpSem.{op} {b} c = {le}", [], int(a)))
            continue
        # binary const folds
        m = re.fullmatch(r"\((Add|Sub|Mul|And|Or|Xor|Div|Mod)(8|16|32|64)(u?)\s+\(Const\2\s+\[c\]\)\s+\(Const\2\s+\[d\]\)\)\s*(?:&&\s*(.*?)\s*)?=>\s*\(Const\2\s+\[(.*)\]\)", s)
        if m:
            op, w, u, cond, expr = m.groups()
            key = op + ("u" if u else "")
            if key not in BIN: skipped.append((lineno, s)); continue
            le = lean_expr(expr, int(w))
            if le is None: skipped.append((lineno, s)); continue
            hyps = []
            if cond:
                if cond.replace(" ", "") == "d!=0": hyps.append(f"(_hd : d ≠ 0)")
                else: skipped.append((lineno, s)); continue
            name = f"{op}{w}{u}_fold"
            thms.append((name, lineno, s, f"(c d : BitVec {w})", f"OpSem.{BIN[key]} c d = {le}", hyps, int(w)))
            continue
        # unary
        m = re.fullmatch(r"\((Neg|Com)(8|16|32|64)\s+\(Const\2\s+\[c\]\)\)\s*=>\s*\(Const\2\s+\[(.*)\]\)", s)
        if m:
            op, w, expr = m.groups()
            le = lean_expr(expr, int(w))
            if le is None: skipped.append((lineno, s)); continue
            thms.append((f"{op}{w}_fold", lineno, s, f"(c : BitVec {w})", f"OpSem.{UN[op]} c = {le}", [], int(w)))
            continue
        # shifts by Const64
        m = re.fullmatch(r"\((Lsh|Rsh)(8|16|32|64)(U?)x64\s+\(Const\2\s+\[c\]\)\s+\(Const64\s+\[d\]\)\)\s*=>\s*\(Const\2\s+\[(.*)\]\)", s)
        if m:
            op, w, u, expr = m.groups()
            le = lean_expr(expr, int(w))
            if le is None: skipped.append((lineno, s)); continue
            sem = {"Lsh": "lsh", "Rsh": "rsh", "RshU": "rshu"}[op + u]
            thms.append((f"{op}{w}{u}x64_fold", lineno, s, f"(c : BitVec {w}) (d : BitVec 64)", f"OpSem.{sem} c d = {le}", [], int(w)))
            continue
        if re.match(r"\((Add|Sub|Mul|And|Or|Xor|Div|Mod|Neg|Com|Lsh|Rsh|Trunc|ZeroExt|SignExt)\w*\s+\(Const", s):
            skipped.append((lineno, s))
    out = []
    out.append("-- Code generated by scripts/rules_to_lean.py from generic.rules. DO NOT EDIT.")
    out.append(f"-- Source: $GOROOT/src/cmd/compile/internal/ssa/_gen/generic.rules sha256 {sha}")
    out.append(f"-- {len(thms)} constant-folding rules translated; {len(skipped)} constant rules not translated (listed at the end).")
    out.append("import Std.Tactic.BVDecide\nimport GoInLean.Compiler.OpSem\n")
    out.append("namespace Go.Compiler.GeneratedFolds\nopen Go.Compiler\n")
    for name, lineno, rule, binders, stmt, hyps, w in thms:
        if name in seen: name += f"_L{lineno}"
        seen.add(name)
        out.append(f"/-- generic.rules:{lineno}  `{rule}` -/")
        hyp = (" " + " ".join(hyps)) if hyps else ""
        # proof: unfolding the operation semantics usually closes the goal by reflexivity;
        # anything left is a fixed-width identity for decide (width 8) or bv_decide.
        body = "  unfold_sem <;> first | rfl | decide | bv_decide"
        out.append(f"theorem {name} {binders}{hyp} :\n    {stmt} := by\n{body}\n")
    out.append("end Go.Compiler.GeneratedFolds\n")
    out.append("/-! ## Constant rules not translated (manual review needed)\n")
    for lineno, s in skipped:
        out.append(f"-- generic.rules:{lineno}  {s}")
    out.append("-/")
    text = "\n".join(out) + "\n"
    # the unfold_sem macro goes right after the namespace line
    text = text.replace("namespace Go.Compiler.GeneratedFolds\nopen Go.Compiler\n",
        "namespace Go.Compiler.GeneratedFolds\nopen Go.Compiler\n\n"
        "macro \"unfold_sem\" : tactic => `(tactic| simp only [OpSem.add, OpSem.sub, OpSem.mul, OpSem.and, OpSem.or, OpSem.xor,\n"
        "  OpSem.div, OpSem.mod, OpSem.divu, OpSem.modu, OpSem.neg, OpSem.com, OpSem.lsh, OpSem.rsh, OpSem.rshu,\n"
        "  OpSem.trunc, OpSem.zeroExt, OpSem.signExt])\n")
    if "--check" in sys.argv:
        if open(OUT).read() != text:
            raise SystemExit("GeneratedFolds.lean is out of date; rerun scripts/rules_to_lean.py")
        print("GeneratedFolds.lean up to date"); return
    open(OUT, "w").write(text)
    print(f"wrote {os.path.relpath(OUT)}: {len(thms)} theorems, {len(skipped)} rules skipped")

if __name__ == "__main__":
    main()
