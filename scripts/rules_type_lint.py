#!/usr/bin/env python3
"""Lint SSA rule files for width-inconsistent type annotations on the right-hand side.

For every RHS node `(Op <T> ...)` whose op has a known result width (ConstN, generic integer
ops with a width suffix, LshNx*, RshN*x*, TruncAtoB, ZeroExtAtoB, SignExtAtoB), the width of
`T` is resolved from the left-hand side when possible:
  * a type variable `t` bound by `(OpN <t> ...)` on the LHS has width N;
  * `x.Type` for a pattern variable x in an argument position of a width-N generic op;
  * `v.Type` is the width of the LHS root;
  * `typ.Int8 … typ.UInt64`, `typ.Int`/`typ.UInt`/`typ.Uintptr` (64-bit targets).
Known benign patterns it also reports (triaged on master babb75be, 2026-11-02): lowering
rules that type a 64-bit op with the narrow Go type ("we ignore high parts of registers"),
divmod.rules expansions whose value fits the narrow type, and `typ.Int` in rules guarded by
`config.PtrSize == 4` (32-bit targets; the lint assumes 64-bit `int`).
A mismatch is the defect class of golang/go#81868 and golang/go#82767 (a Const64 or 64-bit op
typed with a narrower type, which later passes may trust). Output: candidates, not findings.
Usage: rules_type_lint.py GEN_DIR [file.rules ...]
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generic_rules_to_lean import read_rules
from arm64_shift_rules import expand

def tokenize(s):
    return re.findall(r"\(|\)|\[[^\]]*\]|\{[^}]*\}|<[^>]*>|[A-Za-z_][\w.]*:|[^\s()]+", s)

def parse(tokens, i=0):
    t = tokens[i]; bind = None
    if re.fullmatch(r"[A-Za-z_]\w*:", t): bind = t[:-1]; i += 1; t = tokens[i]
    if t == "(":
        op = tokens[i + 1]; i += 2; typ = None; args = []
        while tokens[i] != ")":
            tk = tokens[i]
            if tk.startswith("<"): typ = tk[1:-1]; i += 1
            elif tk.startswith("[") or tk.startswith("{"): i += 1
            else:
                a, i = parse(tokens, i); args.append(a)
        return ("op", op, typ, args, bind), i + 1
    return ("var", t), i + 1

def width(op):
    """result width and per-argument widths for ops we understand (None if unknown)."""
    m = re.fullmatch(r"Const(8|16|32|64)", op)
    if m: return int(m.group(1)), []
    m = re.fullmatch(r"(Add|Sub|Mul|And|Or|Xor|Div|Mod|Hmul|Avg)(8|16|32|64)u?", op)
    if m: n = int(m.group(2)); return n, [n, n]
    m = re.fullmatch(r"(Neg|Com|Ctz|BitLen|PopCount|Bswap|BitRev)(8|16|32|64)", op)
    if m:
        n = int(m.group(2))
        return (n if m.group(1) in ("Neg", "Com", "Bswap", "BitRev") else None), [n]
    m = re.fullmatch(r"(Lsh|Rsh)(8|16|32|64)U?x(8|16|32|64)", op)
    if m: return int(m.group(2)), [int(m.group(2)), int(m.group(3))]
    m = re.fullmatch(r"(Trunc|ZeroExt|SignExt)(8|16|32|64)to(8|16|32|64)", op)
    if m: return int(m.group(3)), [int(m.group(2))]
    m = re.fullmatch(r"RotateLeft(8|16|32|64)", op)
    if m: n = int(m.group(1)); return n, [n, None]
    m = re.fullmatch(r"(Eq|Neq|Less|Leq)(8|16|32|64)U?", op)
    if m: n = int(m.group(2)); return None, [n, n]
    return None, []

TYP = {"typ.Int8": 8, "typ.UInt8": 8, "typ.Int16": 16, "typ.UInt16": 16, "typ.Int32": 32, "typ.UInt32": 32,
       "typ.Int64": 64, "typ.UInt64": 64, "typ.Int": 64, "typ.UInt": 64, "typ.Uintptr": 64}

def lint_rule(rule):
    lhs, rhs = rule.split("=>", 1)
    pat = lhs.split("&&", 1)[0]
    try:
        L, _ = parse(tokenize(pat.strip())); R, _ = parse(tokenize(rhs.strip()))
    except (IndexError, ValueError):
        return []
    tvars, vtypes = {}, {}
    def walk_l(e, expect):
        if e[0] == "var":
            if expect: vtypes.setdefault(e[1], expect)
            return
        _, op, typ, args, bind = e
        rw, aw = width(op)
        if rw is None and expect: rw = expect if op.startswith("Const") else rw
        if typ and re.fullmatch(r"\w+", typ) and rw: tvars.setdefault(typ, rw)
        if bind and rw: vtypes.setdefault(bind, rw)
        for k, a in enumerate(args):
            walk_l(a, aw[k] if k < len(aw) else None)
    walk_l(L, None)
    root_w = width(L[1])[0]
    issues = []
    def resolve(T):
        if T in tvars: return tvars[T]
        if T in TYP: return TYP[T]
        if T == "v.Type": return root_w
        m = re.fullmatch(r"(\w+)\.Type", T)
        if m and m.group(1) in vtypes: return vtypes[m.group(1)]
        return None
    def walk_r(e):
        if e[0] == "var": return
        _, op, typ, args, bind = e
        rw, _ = width(op)
        if typ and rw:
            tw = resolve(typ)
            if tw and tw != rw:
                issues.append(f"({op} <{typ}>): op width {rw}, type width {tw}")
        for a in args: walk_r(a)
    walk_r(R)
    return issues

def main():
    d = sys.argv[1]
    files = sys.argv[2:] or sorted(f for f in os.listdir(d) if f.endswith(".rules"))
    n = 0
    for f in files:
        for ln, rule in read_rules(open(os.path.join(d, f)).read()):
            try: insts = expand(rule)
            except ValueError: insts = [rule]
            seen = set()
            for r in insts:
                for issue in lint_rule(re.sub(r"\b(ssa|ssaop)\.", "", r)):
                    if issue in seen: continue
                    seen.add(issue); n += 1
                    print(f"{f}:{ln}: {issue}\n    {r[:200]}")
    print(f"{n} width-inconsistent annotations")

if __name__ == "__main__":
    main()
