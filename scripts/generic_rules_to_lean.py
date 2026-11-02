#!/usr/bin/env python3
"""Translate value-level rules of generic.rules into Lean theorems, with automatic triage.

Supported: integer and boolean generic ops on fixed widths (Add/Sub/Mul/And/Or/Xor/Neg/Com,
Lsh/Rsh/RshU NxM, Trunc/ZeroExt/SignExt, Eq/Neq/Less/Leq[U], Const*, ConstBool, Not, AndB, OrB,
EqB, NeqB, CvtBoolToUint8), pattern variables, `name:(...)` bindings, `_`, AuxInt variables, and a
typed subset of Go expressions in AuxInts and conditions (+ - * & | ^ &^ << >> / %, comparisons,
&& || !, conversions intN/uintN, helpers isPowerOfTwo, logN, ntzN, nlzN, oneBitN, uaddOvf,
is32Bit, b2i). Div/Mod ops (panic semantics), floats, memory, calls, blocks are out of scope.

Conditions that do not constrain values (`x.Op != OpConst8`, `.Uses`, `clobber`, `config.`,
`v.Type`, `canonLessThan`, ...) are DROPPED: the theorem then states a stronger claim, so a
proof remains valid; a counterexample is triaged, never claimed. Conditions mentioning
`isNonNegative` or other value facts we cannot express make the rule SKIPPED.

Modes:
  (default)  generate GoInLean/Compiler/GeneratedRules.lean, excluding ids listed in
             targets/generic_rules_triage.json
  --triage   generate all, run `lake env lean` per chunk, record each failing rule's category
             (counterexample / timeout / spurious / elab_error) in the triage file, then
             regenerate without them
  --check    verify the committed file is up to date
"""
import hashlib, json, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from arm64_shift_rules import expand

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
GOROOT = os.environ.get("GOROOT") or subprocess.check_output(["go", "env", "GOROOT"], text=True).strip()
RULES = os.path.join(GOROOT, "src/cmd/compile/internal/ssa/_gen/generic.rules")
OUT = os.path.join(ROOT, "GoInLean", "Compiler", "GeneratedRules.lean")
TRIAGE = os.path.join(ROOT, "targets", "generic_rules_triage.json")

class Skip(Exception):
    pass

# ---------------------------------------------------------------- rule reading
def read_rules(src):
    rules, cur, start = [], "", 0
    for lineno, line in enumerate(src.splitlines(), 1):
        code = line.split("//")[0].rstrip()
        if not cur:
            if code.startswith("("):
                cur, start = code, lineno
            else:
                continue
        else:
            cur += " " + code.strip()
        if cur.count("(") == cur.count(")") and "=>" in cur and not cur.rstrip().endswith("=>"):
            rules.append((start, cur.strip())); cur = ""
    return rules

def tokenize(s):
    return re.findall(r"\(|\)|\[[^\]]*\]|\{[^}]*\}|<[^>]*>|[A-Za-z_][\w.]*:|[^\s()]+", s)

def parse(tokens, i=0):
    t = tokens[i]
    bind = None
    if re.fullmatch(r"[A-Za-z_]\w*:", t):
        bind = t[:-1]; i += 1; t = tokens[i]
    if t == "(":
        op = tokens[i + 1]; i += 2
        aux, typ, args = None, None, []
        while tokens[i] != ")":
            tk = tokens[i]
            if tk.startswith("["):
                aux = tk[1:-1]; i += 1
            elif tk.startswith("<"):
                typ = tk[1:-1]; i += 1
            elif tk.startswith("{"):
                raise Skip("aux {..}")
            else:
                a, i = parse(tokens, i); args.append(a)
        return ("op", op, aux, args, bind), i + 1
    if bind:
        raise Skip("binding on leaf")
    return ("var", t), i + 1

# ---------------------------------------------------------------- op table
def opinfo(op):
    """returns (kind, result_type, arg_types) with types 'bvN' or 'bool'"""
    m = re.fullmatch(r"(Add|Sub|Mul|And|Or|Xor)(8|16|32|64)", op)
    if m: n = m.group(2); return (m.group(1).lower(), f"bv{n}", [f"bv{n}", f"bv{n}"])
    m = re.fullmatch(r"(Neg|Com)(8|16|32|64)", op)
    if m: n = m.group(2); return (m.group(1).lower(), f"bv{n}", [f"bv{n}"])
    m = re.fullmatch(r"(Lsh|Rsh)(8|16|32|64)(U?)x(8|16|32|64)", op)
    if m:
        n, a = m.group(2), m.group(4)
        return ({"Lsh": "lsh", "Rsh": "rsh", "RshU": "rshu"}[m.group(1) + m.group(3)], f"bv{n}", [f"bv{n}", f"bv{a}"])
    m = re.fullmatch(r"(Trunc|ZeroExt|SignExt)(8|16|32|64)to(8|16|32|64)", op)
    if m: return (m.group(1).lower(), f"bv{m.group(3)}", [f"bv{m.group(2)}"])
    m = re.fullmatch(r"(Eq|Neq|Less|Leq)(8|16|32|64)(U?)", op)
    if m: n = m.group(2); return ((m.group(1) + m.group(3)).lower(), "bool", [f"bv{n}", f"bv{n}"])
    m = re.fullmatch(r"Const(8|16|32|64)", op)
    if m: return ("const", f"bv{m.group(1)}", [])
    m = re.fullmatch(r"(Div|Mod)(8|16|32|64)(u?)", op)
    if m: n = m.group(2); return ((m.group(1) + m.group(3)).lower(), f"bv{n}", [f"bv{n}", f"bv{n}"])
    m = re.fullmatch(r"Hmul(32|64)(u?)", op)
    if m: n = m.group(1); return ("hmul" + m.group(2), f"bv{n}", [f"bv{n}", f"bv{n}"])
    if op == "Avg64u": return ("avg", "bv64", ["bv64", "bv64"])
    if op == "Avg32u": return ("avg", "bv32", ["bv32", "bv32"])
    if op == "ConstBool": return ("constb", "bool", [])
    if op == "Not": return ("not", "bool", ["bool"])
    if op in ("AndB", "OrB", "EqB", "NeqB"): return (op.lower(), "bool", ["bool", "bool"])
    if op == "CvtBoolToUint8": return ("b2u8", "bv8", ["bool"])
    raise Skip("op " + op)

def lean_type(t):
    return "Bool" if t == "bool" else f"BitVec {t[2:]}"

# ---------------------------------------------------------------- Go expression translator
GO_PREC = [("||",), ("&&",), ("==", "!=", "<", "<=", ">", ">="), ("+", "-", "|", "^"),
           ("*", "/", "%", "<<", ">>", "&", "&^")]

def gtok(s):
    return re.findall(r"0[xX][0-9a-fA-F]+|\d+|[A-Za-z_][\w.]*|&\^|<<|>>|<=|>=|==|!=|&&|\|\||[-+*/%&|^!<>(),]", s)

class GoExpr:
    def __init__(self, s, env):
        self.t, self.i, self.env = gtok(s), 0, env
        if not self.t: raise Skip("empty expr")
    def peek(self): return self.t[self.i] if self.i < len(self.t) else None
    def eat(self): x = self.t[self.i]; self.i += 1; return x
    def parse(self):
        v = self.binary(0)
        if self.peek() is not None: raise Skip("trailing tokens")
        return v
    def binary(self, lvl):
        if lvl == len(GO_PREC): return self.unary()
        left = self.binary(lvl + 1)
        while self.peek() in GO_PREC[lvl]:
            op = self.eat(); right = self.binary(lvl + 1)
            left = combine(op, left, right)
        return left
    def unary(self):
        p = self.peek()
        if p in ("-", "^", "!"):
            self.eat(); v = self.unary()
            if p == "!":
                if v[1] != "bool": raise Skip("! on int")
                return (f"(!{v[0]})", "bool")
            if v[1] == "untyped": return (("-" if p == "-" else "~~~") + v[0], "untyped", (-v[2] if p == "-" else ~v[2]))
            return (f"({'-' if p == '-' else '~~~'}{v[0]})", v[1])
        return self.primary()
    def primary(self):
        p = self.eat()
        if p == "(":
            v = self.binary(0)
            if self.eat() != ")": raise Skip("paren")
            return v
        if re.fullmatch(r"0[xX][0-9a-fA-F]+|\d+", p):
            n = int(p, 0); return (str(n), "untyped", n)
        if p in ("true", "false"): return (p, "bool")
        if self.peek() == "(":
            self.eat(); args = []
            if self.peek() != ")":
                args.append(self.binary(0))
                while self.peek() == ",":
                    self.eat(); args.append(self.binary(0))
            if self.eat() != ")": raise Skip("call")
            return call(p, args)
        if p in self.env: return self.env[p]
        consts = {"math.MaxInt8": 127, "math.MaxInt16": 32767, "math.MaxInt32": 2**31 - 1, "math.MaxInt64": 2**63 - 1,
                  "math.MinInt8": -128, "math.MinInt16": -32768, "math.MinInt32": -2**31, "math.MinInt64": -2**63,
                  "math.MaxUint8": 255, "math.MaxUint16": 65535, "math.MaxUint32": 2**32 - 1, "math.MaxUint64": 2**64 - 1}
        if p in consts: return (str(consts[p]), "untyped", consts[p])
        raise Skip("ident " + p)

def as_type(v, t):
    """coerce untyped constant v to typed t"""
    if v[1] == "untyped":
        if t == "bool": raise Skip("untyped to bool")
        w = int(t[1:].split("u")[0]) if False else None
        return (f"(BitVec.ofInt {width(t)} ({v[2]}))", t)
    return v

def width(t): return int(re.sub(r"[^0-9]", "", t))
def signed(t): return t.startswith("i")

def unify(a, b):
    if a[1] == "untyped" and b[1] == "untyped":
        raise Skip("const-only expression")
    if a[1] == "untyped": a = as_type(a, b[1])
    if b[1] == "untyped": b = as_type(b, a[1])
    if a[1] != b[1]: raise Skip(f"type mismatch {a[1]} {b[1]}")
    return a, b

def fold(op, x, y):
    return {"+": lambda: x + y, "-": lambda: x - y, "*": lambda: x * y, "&": lambda: x & y,
            "|": lambda: x | y, "^": lambda: x ^ y, "&^": lambda: x & ~y, "<<": lambda: x << y,
            ">>": lambda: x >> y}.get(op, lambda: None)()

def combine(op, a, b):
    if a[1] == "untyped" and b[1] == "untyped":
        v = fold(op, a[2], b[2])
        if v is None: raise Skip("const-only expression")
        return (str(v), "untyped", v)
    if op in ("&&", "||"):
        if a[1] != "bool" or b[1] != "bool": raise Skip("bool op")
        return (f"({a[0]} {op} {b[0]})", "bool")
    if op in ("<<", ">>"):
        if a[1] == "untyped": raise Skip("untyped shift base")
        if b[1] == "untyped": b = (f"(BitVec.ofNat 64 {b[2]})", "u64")
        # a signed count is legal Go (it panics if negative at run time); rules guard it
        # with `c >= 0`, so its bit pattern is the unsigned amount.
        amt = b[0] if width(b[1]) == 64 else f"({b[0]}.setWidth 64)"
        if op == "<<": return (f"({a[0]} <<< {amt})", a[1])
        return (f"({a[0]}.sshiftRight' {amt})" if signed(a[1]) else f"({a[0]} >>> {amt})", a[1])
    if a[1] == "bool" or b[1] == "bool":
        if op in ("==", "!=") and a[1] == b[1] == "bool":
            return (f"({a[0]} {'==' if op == '==' else '!='} {b[0]})", "bool")
        raise Skip("bool arith")
    a, b = unify(a, b)
    t = a[1]; s = signed(t)
    if op in ("+", "-", "*"): return (f"({a[0]} {op} {b[0]})", t)
    if op == "&": return (f"({a[0]} &&& {b[0]})", t)
    if op == "|": return (f"({a[0]} ||| {b[0]})", t)
    if op == "^": return (f"({a[0]} ^^^ {b[0]})", t)
    if op == "&^": return (f"({a[0]} &&& ~~~{b[0]})", t)
    if op == "/": return (f"({a[0]}.sdiv {b[0]})" if s else f"({a[0]} / {b[0]})", t)
    if op == "%": return (f"({a[0]}.srem {b[0]})" if s else f"({a[0]} % {b[0]})", t)
    if op == "==": return (f"({a[0]} == {b[0]})", "bool")
    if op == "!=": return (f"({a[0]} != {b[0]})", "bool")
    lt = (lambda x, y: f"({x}.slt {y})") if s else (lambda x, y: f"(decide ({x} < {y}))")
    le = (lambda x, y: f"({x}.sle {y})") if s else (lambda x, y: f"(decide ({x} ≤ {y}))")
    if op == "<": return (lt(a[0], b[0]), "bool")
    if op == ">": return (lt(b[0], a[0]), "bool")
    if op == "<=": return (le(a[0], b[0]), "bool")
    if op == ">=": return (le(b[0], a[0]), "bool")
    raise Skip("op " + op)

def convert(v, t):
    if v[1] == "untyped": return as_type(v, t)
    if v[1] == "bool": raise Skip("convert bool")
    w1, w2 = width(v[1]), width(t)
    if w2 <= w1: return (f"({v[0]}.setWidth {w2})", t)
    return ((f"({v[0]}.signExtend {w2})" if signed(v[1]) else f"({v[0]}.setWidth {w2})"), t)

def call(f, args):
    m = re.fullmatch(r"(u?)int(8|16|32|64)", f)
    if m and len(args) == 1:
        return convert(args[0], ("u" if m.group(1) else "i") + m.group(2))
    if f == "int" and len(args) == 1: return convert(args[0], "i64")
    if f == "uint" and len(args) == 1: return convert(args[0], "u64")
    if f == "isPowerOfTwo": return (f"(GSem.isPowerOfTwo {args[0][0]})", "bool")
    m = re.fullmatch(r"log(8|16|32|64)", f)
    if m: return (f"(GSem.lg {args[0][0]})", "i64")
    m = re.fullmatch(r"(ntz|nlz)(8|16|32|64)", f)
    if m: return (f"(GSem.{m.group(1)} {args[0][0]})", "i64")
    m = re.fullmatch(r"oneBit(8|16|32|64)?", f)
    if m: return (f"(GSem.oneBit {args[0][0]})", "bool")
    if f == "uaddOvf": return (f"(GSem.uaddOvf {args[0][0]} {args[1][0]})", "bool")
    if f == "is32Bit": return (f"(GSem.is32Bit {args[0][0]})", "bool")
    if f == "b2i": return (f"(GSem.b2i {args[0][0]})", "i64")
    raise Skip("call " + f)

DROP = re.compile(r"\.Op\b|\.Uses|clobber|config\.|\.Type|canonLessThan|mergePoint|\.Block|isSameCall|"
                  r"\.Aux\b|v\.Args|@|x\.Op|y\.Op|isConstZero|\bOp[A-Z]")

def split_conj(cond):
    parts, depth, cur, i = [], 0, "", 0
    while i < len(cond):
        c = cond[i]
        if c == "(": depth += 1
        if c == ")": depth -= 1
        if depth == 0 and cond.startswith("&&", i):
            parts.append(cur.strip()); cur = ""; i += 2; continue
        cur += c; i += 1
    parts.append(cur.strip())
    return [p for p in parts if p]

# ---------------------------------------------------------------- one rule
def translate(rule):
    lhs_s, rhs_s = rule.split("=>", 1)
    cond = None
    if "&&" in lhs_s:
        # condition starts after the balanced pattern
        depth = 0
        for k, ch in enumerate(lhs_s):
            depth += ch == "("; depth -= ch == ")"
            if depth == 0 and k > 0:
                pat, rest = lhs_s[:k + 1], lhs_s[k + 1:].strip()
                break
        if not rest.startswith("&&"): raise Skip("cond")
        lhs_s, cond = pat, rest[2:].strip()
    if rhs_s.strip().startswith("@") or "..." in rule: raise Skip("block/ellipsis")
    lhs, _ = parse(tokenize(lhs_s))
    rhs, _ = parse(tokenize(rhs_s.strip()))
    vars_, auxv, binds = {}, {}, {}
    nonzero = []
    wild = [0]
    def walk_lhs(e, expect):
        if e[0] == "var":
            name = e[1]
            if name == "_":
                wild[0] += 1; name = f"w{wild[0]}"
            if name in vars_ and vars_[name] != expect: raise Skip("var type clash")
            vars_[name] = expect; return name
        _, op, aux, args, bind = e
        kind, rt, ats = opinfo(op)
        if expect is not None and rt != expect: raise Skip("result type clash")
        if len(args) != len(ats): raise Skip("arity")
        if kind == "const":
            t = "i" + rt[2:]
            if aux is None:
                wild[0] += 1; aux = f"k{wild[0]}"   # matches any constant
            if re.fullmatch(r"[A-Za-z_]\w*", aux):
                if aux in auxv and auxv[aux][1] != t: raise Skip("aux type clash")
                auxv[aux] = (aux, t); s = aux
            else:
                s = as_type(GoExpr(aux, {}).parse(), t)[0]
            out = s
        elif kind == "constb":
            if aux in ("true", "false"): out = aux
            elif re.fullmatch(r"[A-Za-z_]\w*", aux): auxv[aux] = (aux, "bool"); out = aux
            else: raise Skip("constbool aux")
        else:
            subs = [walk_lhs(a, t) for a, t in zip(args, ats)]
            if kind in ("div", "divu", "mod", "modu"):
                nonzero.append(f"({subs[1]} != 0)")
            out = sem(kind, subs, rt)
        if bind:
            binds[bind] = (out, rt)
        return out
    lhs_val = walk_lhs(lhs, None)
    rtype = opinfo(lhs[1])[1]
    env = dict(auxv)
    def walk_rhs(e, expect):
        if e[0] == "var":
            n = e[1]
            if n in binds: return binds[n][0]
            if n in vars_: return n
            raise Skip("unbound rhs var " + n)
        _, op, aux, args, bind = e
        kind, rt, ats = opinfo(op)
        if kind == "const":
            return as_type(GoExpr(aux, env).parse(), "i" + rt[2:])[0] if aux is not None else f"(0 : BitVec {rt[2:]})"
        if kind == "constb":
            v = GoExpr(aux, env).parse()
            if v[1] != "bool": raise Skip("constbool expr")
            return v[0]
        subs = [walk_rhs(a, t) for a, t in zip(args, ats)]
        return sem(kind, subs, rt)
    rhs_val = walk_rhs(rhs, rtype)
    hyps = list(nonzero)
    if cond:
        for c in split_conj(cond):
            if DROP.search(c):
                continue
            if "isNonNegative" in c: raise Skip("isNonNegative")
            v = GoExpr(c, env).parse()
            if v[1] != "bool": raise Skip("non-bool cond")
            hyps.append(v[0])
    binders = []
    for n, t in vars_.items(): binders.append(f"({n} : {lean_type(t)})")
    for n, (_, t) in auxv.items():
        binders.append(f"({n} : {'Bool' if t == 'bool' else 'BitVec ' + str(width(t))})")
    return binders, hyps, lhs_val, rhs_val, rtype

def sem(kind, s, rt):
    w = rt[2:] if rt.startswith("bv") else None
    if kind in ("add", "sub", "mul"): return f"({s[0]} {dict(add='+', sub='-', mul='*')[kind]} {s[1]})"
    if kind == "and": return f"({s[0]} &&& {s[1]})"
    if kind == "or": return f"({s[0]} ||| {s[1]})"
    if kind == "xor": return f"({s[0]} ^^^ {s[1]})"
    if kind == "neg": return f"(-{s[0]})"
    if kind == "com": return f"(~~~{s[0]})"
    if kind == "lsh": return f"({s[0]} <<< {s[1]})"
    if kind == "rshu": return f"({s[0]} >>> {s[1]})"
    if kind == "rsh": return f"({s[0]}.sshiftRight' {s[1]})"
    if kind in ("trunc", "zeroext"): return f"({s[0]}.setWidth {w})"
    if kind == "signext": return f"({s[0]}.signExtend {w})"
    if kind == "eq": return f"({s[0]} == {s[1]})"
    if kind == "neq": return f"({s[0]} != {s[1]})"
    if kind == "less": return f"({s[0]}.slt {s[1]})"
    if kind == "leq": return f"({s[0]}.sle {s[1]})"
    if kind == "lessu": return f"(decide ({s[0]} < {s[1]}))"
    if kind == "lequ": return f"(decide ({s[0]} ≤ {s[1]}))"
    if kind == "not": return f"(!{s[0]})"
    if kind == "andb": return f"({s[0]} && {s[1]})"
    if kind == "orb": return f"({s[0]} || {s[1]})"
    if kind == "eqb": return f"({s[0]} == {s[1]})"
    if kind == "neqb": return f"({s[0]} != {s[1]})"
    if kind == "b2u8": return f"(if {s[0]} then (1 : BitVec 8) else 0)"
    # Division: the generic ops only execute with a non-zero divisor (the divide-by-zero
    # panic check is a separate SSA value); `translate` adds `divisor != 0` hypotheses.
    if kind == "div": return f"({s[0]}.sdiv {s[1]})"
    if kind == "divu": return f"({s[0]} / {s[1]})"
    if kind == "mod": return f"({s[0]}.srem {s[1]})"
    if kind == "modu": return f"({s[0]} % {s[1]})"
    if kind == "hmul": return f"((({s[0]}.signExtend (2*{w})) * ({s[1]}.signExtend (2*{w}))).extractLsb' {w} {w})"
    if kind == "hmulu": return f"((({s[0]}.setWidth (2*{w})) * ({s[1]}.setWidth (2*{w}))).extractLsb' {w} {w})"
    if kind == "avg": return f"((({s[0]}.setWidth ({w}+1)) + ({s[1]}.setWidth ({w}+1))) >>> 1).setWidth {w}"
    raise Skip(kind)

UNFOLD = ("simp only [GSem.isPowerOfTwo, GSem.lg, GSem.ntz, GSem.nlz, GSem.oneBit, GSem.uaddOvf, GSem.is32Bit,"
          " GSem.b2i, BitSpec.len, BitSpec.ctz, BitSpec.clz, List.range, List.range.loop, List.foldl, List.foldr] at *")

def theorem(tid, lineno, rule, tr):
    binders, hyps, lhs, rhs, rt = tr
    hs = "".join(f"\n    (h{k} : {h} = true)" for k, h in enumerate(hyps))
    return (f"/-- generic.rules:{lineno}  `{rule}` -/\n"
            f"theorem {tid} {' '.join(binders)}{hs} :\n    {rhs} = {lhs} := by\n"
            f"  first | rfl | ({UNFOLD} <;> bv_decide) | bv_decide\n")

HEADER = """-- Code generated by scripts/generic_rules_to_lean.py from generic.rules. DO NOT EDIT.
-- Source: $GOROOT/src/cmd/compile/internal/ssa/_gen/generic.rules sha256 {sha}
-- {n} rule instances translated and proved; {ex} excluded after triage
-- (targets/generic_rules_triage.json); {sk} rules outside the supported fragment.
-- Each theorem: (right-hand side) = (left-hand side), for all values, under the rule's
-- value-level condition (non-semantic conditions dropped, which only strengthens the claim).
import Std.Tactic.BVDecide
import GoInLean.Compiler.GenericSem

set_option maxRecDepth 8192
namespace Go.Compiler.GeneratedRules
open Go.Compiler Go

"""

def collect():
    src = open(RULES).read()
    sha = hashlib.sha256(src.encode()).hexdigest()
    items, skipped = [], {}
    for lineno, rule in read_rules(src):
        try:
            insts = expand(rule)
        except ValueError:
            skipped["alternation"] = skipped.get("alternation", 0) + 1; continue
        for k, r in enumerate(insts):
            tid = f"r{lineno}_{k}"
            try:
                items.append((tid, lineno, r, translate(r)))
            except Skip as e:
                key = str(e).split(" ")[0]
                skipped[key] = skipped.get(key, 0) + 1
            except (IndexError, KeyError, ValueError) as e:
                skipped["parse"] = skipped.get("parse", 0) + 1
    return sha, items, skipped

def render(sha, items, excluded, nskip):
    keep = [it for it in items if it[0] not in excluded]
    text = HEADER.format(sha=sha, n=len(keep), ex=len(excluded), sk=nskip)
    text += "\n".join(theorem(*it) for it in keep)
    text += "\nend Go.Compiler.GeneratedRules\n"
    return text

def lean_check(text):
    tmp = os.path.join(ROOT, "build", "GeneratedRulesTriage.lean")
    os.makedirs(os.path.dirname(tmp), exist_ok=True)
    open(tmp, "w").write(text)
    r = subprocess.run(["lake", "env", "lean", tmp], cwd=ROOT, text=True, capture_output=True, timeout=7200)
    out = r.stdout + r.stderr
    if r.returncode != 0 and ": error" not in out:
        raise SystemExit("lean failed without reporting errors (crash/panic?):\n" + out[-2000:])
    if "PANIC" in out or "INTERNAL" in out:
        raise SystemExit("lean reported an internal panic:\n" + out[-2000:])
    return text, out

def triage():
    sha, items, skipped = collect()
    print(f"{len(items)} rule instances translated; skipped: {skipped}")
    text = render(sha, items, set(), sum(skipped.values()))
    text, out = lean_check(text)
    # map error line -> theorem id
    starts = [(m.start(), m.group(1)) for m in re.finditer(r"^theorem (\w+)", text, re.M)]
    line_of = lambda pos: text.count("\n", 0, pos) + 1
    tline = [(line_of(p), t) for p, t in starts]
    result = {}
    for m in re.finditer(r"GeneratedRulesTriage\.lean:(\d+):\d+: error: (.*)", out):
        ln, msg = int(m.group(1)), m.group(2)
        tid = None
        for l, t in tline:
            if l <= ln: tid = t
        if tid is None: continue
        seg = out[m.start(): m.start() + 600]
        seg = re.split(r"\n[^\n]*\.lean:\d+:\d+: error", seg, maxsplit=1)[0]   # this error only
        if "found a counterexample" in seg and "potentially spurious" not in seg:
            cat = "counterexample"
        elif "potentially spurious" in seg: cat = "spurious"
        elif "timed out" in seg or "timeout" in seg: cat = "timeout"
        else: cat = "elab_error"
        if tid not in result:
            result[tid] = {"category": cat, "message": seg.split("\n")[0][:300],
                           "detail": seg[:600]}
    for tid, lineno, r, _ in items:
        if tid in result: result[tid]["rule"] = r; result[tid]["line"] = lineno
    json.dump(result, open(TRIAGE, "w"), indent=1, sort_keys=True)
    cats = {}
    for v in result.values(): cats[v["category"]] = cats.get(v["category"], 0) + 1
    print(f"triage: {len(result)} failures {cats}")
    final = render(sha, items, set(result), sum(skipped.values()))
    open(OUT, "w").write(final)
    print(f"wrote {os.path.relpath(OUT, ROOT)}: {len(items) - len(result)} theorems")

def main():
    if "--triage" in sys.argv:
        return triage()
    sha, items, skipped = collect()
    excluded = set(json.load(open(TRIAGE))) if os.path.exists(TRIAGE) else set()
    text = render(sha, items, excluded, sum(skipped.values()))
    if "--check" in sys.argv:
        if open(OUT).read() != text: raise SystemExit("GeneratedRules.lean is out of date; rerun with --triage")
        print("GeneratedRules.lean up to date"); return
    open(OUT, "w").write(text)
    print(f"wrote {os.path.relpath(OUT, ROOT)}: {len(items) - len(excluded)} theorems; skipped {skipped}")

if __name__ == "__main__":
    main()
