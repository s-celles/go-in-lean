#!/usr/bin/env python3
"""Translation validation of gc's generic SSA passes with z3.

gc can dump a function's SSA after every pass (`-d=ssa/all/dump=F`). For the
loop-free integer functions of the alternative-compiler campaign, each dump of
the generic (architecture-independent) part of the pipeline, from `build` up to
`lower`, is encoded as a z3 bit-vector formula of the parameters: the outcome
(return, or the runtime panic that ends the function) and the returned value.

Two checks, for all inputs at once rather than on sampled ones:

* equivalence of consecutive passes: some (x, y) giving a different outcome or
  value is a counterexample, and names the pass that introduced the change;
* facts the compiler claims in the IR: a shift marked bounded (`[true]`) needs
  its count below the width; a signed division or modulo marked `[true]`
  needs to avoid MinInt / -1; every division needs a nonzero divisor where it
  is reached; Avg needs arg0 >= arg1. A violated fact is a miscompilation
  even if the pass that made the claim did not change the value yet (the
  lowering trusts it).

Functions with memory operations, loops, tuples or unmodelled ops are reported
as unsupported and skipped. The lowered, architecture-specific passes are out
of scope.

  python3 scripts/ssa_tv.py check main.go [--go GO] [--goarch A] [--funcs v0,v1]
  python3 scripts/ssa_tv.py gen --suite core --seed 7 --count 20 [--go GO] [--goarch A]
"""

import argparse
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile

import z3

M64 = (1 << 64) - 1
WIDTH = {"int8": 8, "uint8": 8, "int16": 16, "uint16": 16, "int32": 32, "uint32": 32,
         "int64": 64, "uint64": 64, "int": 64, "uint": 64, "uintptr": 64, "bool": 1}
MEM_OPS = {"InitMem", "Copy", "Phi", "InlMark", "StaticCall", "StaticLECall", "MakeResult"}
PANICS = ("runtime.panicdivide", "runtime.panicshift", "runtime.panicoverflow")


class Unsupported(Exception):
    """The function uses something this encoding does not model."""


class Value:
    __slots__ = ("id", "op", "type", "auxint", "aux", "args", "block")

    def __init__(self, vid, op, typ, auxint, aux, args, block):
        self.id, self.op, self.type, self.auxint, self.aux = vid, op, typ, auxint, aux
        self.args, self.block = args, block


class Block:
    def __init__(self, name, preds):
        self.name, self.preds = name, preds
        self.values, self.kind, self.controls, self.succs = [], None, [], []


class Func:
    def __init__(self, name):
        self.name, self.blocks, self.values = name, [], {}

    def block(self, name):
        return next(b for b in self.blocks if b.name == name)

    def entry(self):
        """The entry block: not always listed first (e.g. after fuse)."""
        roots = [b for b in self.blocks if not b.preds]
        for b in roots:
            if any(v.op == "InitMem" for v in b.values):
                return b
        return roots[0] if roots else self.blocks[0]


_VALUE = re.compile(r"^\s+\((?:[-+]?\d+|\?)\)\s+(v\d+) = (\w+) <([^>]*)>(.*)$")
_BLOCK = re.compile(r"^  (b\d+):(?: <- (.*))?$")
_CTRL = re.compile(r"^    ([A-Z]\w*)\b(.*)$")


def _bracketed(s, i, open_, close):
    depth = 0
    for j in range(i, len(s)):
        depth += s[j] == open_
        depth -= s[j] == close
        if depth == 0:
            return s[i + 1:j], j + 1
    raise ValueError(f"unbalanced {open_} in {s!r}")


def _parse_rest(rest):
    """auxint, aux and arguments of a value line (after its type)."""
    auxint = aux = None
    args = []
    i = 0
    while i < len(rest):
        c = rest[i]
        if c in "[{":
            try:
                inner, i = _bracketed(rest, i, c, "]" if c == "[" else "}")
            except ValueError:  # e.g. a ConstString holding brackets: keep it opaque
                aux = rest[i:]
                break
            if c == "[":
                auxint = inner
            else:
                aux = inner
        elif c == "(":
            break  # trailing user names, e.g. (t1[int16])
        elif c == "v" and re.match(r"v\d+\b", rest[i:]) and (i == 0 or rest[i - 1] == " "):
            m = re.match(r"v\d+", rest[i:])
            args.append(m.group(0))
            i += len(m.group(0))
        else:
            i += 1
    return auxint, aux, args


def parse_dump(text):
    lines = text.splitlines()
    f = Func(lines[0].split()[0])
    blk = None
    for line in lines[1:]:
        if line.startswith("name ") or not line.strip():
            continue
        m = _BLOCK.match(line)
        if m:
            blk = Block(m.group(1), m.group(2).split() if m.group(2) else [])
            f.blocks.append(blk)
            continue
        m = _VALUE.match(line)
        if m:
            auxint, aux, args = _parse_rest(m.group(4))
            v = Value(m.group(1), m.group(2), m.group(3), auxint, aux, args, blk.name)
            blk.values.append(v)
            f.values[v.id] = v
            continue
        m = _CTRL.match(line)
        if m and blk is not None:
            blk.kind = m.group(1)
            rest = re.sub(r"\(\w+\)\s*$", "", m.group(2))  # (likely)/(unlikely)
            head, _, tail = rest.partition("->")
            blk.controls = re.findall(r"v\d+", head)
            blk.succs = re.findall(r"b\d+", tail)
            continue
        raise ValueError(f"unrecognised dump line: {line!r}")
    return f


class _Enc:
    """z3 encoding of one parsed function, in its own context."""

    def __init__(self, f, ctx):
        self.f, self.ctx, self.cache, self.obl = f, ctx, {}, []
        self.params = {}
        self.order = self._topo()
        self.reach = {b.name: z3.BoolVal(False, ctx) for b in f.blocks}
        self.edges = {}
        for b in self.order:
            self._reach(b)

    # ---- helpers
    def bv(self, v, w):
        return z3.BitVecVal(v, w, self.ctx)

    def true(self):
        return z3.BoolVal(True, self.ctx)

    def param(self, name):
        if name not in self.params:
            self.params[name] = z3.BitVec(name, 64, self.ctx)
        return self.params[name]

    def _topo(self):
        blocks = {b.name: b for b in self.f.blocks}
        order, state = [], {}

        def visit(n):
            if state.get(n) == 1:
                raise Unsupported("loop in the CFG")
            if state.get(n) == 2:
                return
            state[n] = 1
            for s in blocks[n].succs:
                if s in blocks:  # a First block may still name a deleted successor
                    visit(s)
            state[n] = 2
            order.append(blocks[n])

        visit(self.f.entry().name)
        return order[::-1]

    def _reach(self, b):
        if b is self.order[0]:  # the entry block
            self.reach[b.name] = self.true()
        else:
            conds, seen = [], {}
            for p in b.preds:
                k = seen.get(p, 0)
                seen[p] = k + 1
                conds.append(self.edges.get((p, b.name, k), z3.BoolVal(False, self.ctx)))
            self.reach[b.name] = z3.Or(*conds) if len(conds) > 1 else conds[0]
        r = self.reach[b.name]
        if b.kind == "If":
            c = self.enc(b.controls[0])
            outs = [z3.And(r, c), z3.And(r, z3.Not(c))]
        elif b.kind in ("Plain", "First"):
            outs = [r] + [z3.BoolVal(False, self.ctx)] * (len(b.succs) - 1)
        elif b.kind in ("Ret", "Exit"):
            outs = []
        else:
            raise Unsupported(f"block kind {b.kind}")
        seen = {}
        for s, cond in zip(b.succs, outs):
            k = seen.get(s, 0)
            seen[s] = k + 1
            self.edges[(b.name, s, k)] = cond

    def oblige(self, v, what, ok):
        self.obl.append((v, what, z3.And(self.reach[v.block], z3.Not(ok))))

    # ---- values
    def enc(self, vid):
        if vid not in self.cache:
            self.cache[vid] = self._enc(self.f.values[vid])
        return self.cache[vid]

    def _width(self, v):
        if v.type not in WIDTH:
            raise Unsupported(f"type {v.type} of {v.id}")
        return WIDTH[v.type]

    def _enc(self, v):
        op, a = v.op, [self.enc(x) for x in v.args] if v.op not in ("Phi",) else None
        ow = op_widths(v) if a is not None else None
        if ow is not None:  # a sized op reads the low bits of a wider value (see fits_type)
            for i, (_, aw) in enumerate(ow[1]):
                if z3.is_bv(a[i]) and a[i].size() > aw:
                    a[i] = z3.Extract(aw - 1, 0, a[i])
        if v.type == "mem" or op in ("MakeResult", "StaticCall", "StaticLECall", "InlMark"):
            if op in MEM_OPS:
                return None
            raise Unsupported(f"memory op {op}")
        if op in ("Arg", "ArgIntReg"):
            if self._width(v) != 64:
                raise Unsupported("non-64-bit parameter")
            return self.param(v.aux.split("+")[0])
        if op == "Copy":
            return a[0]
        if op == "Phi":
            return self._phi(v)
        if op == "ConstBool":
            return z3.BoolVal(v.auxint == "true", self.ctx)
        m = re.fullmatch(r"Const(8|16|32|64)", op)
        if m:
            return self.bv(int(v.auxint) & ((1 << int(m.group(1))) - 1), int(m.group(1)))
        if op == "CondSelect":
            return z3.If(a[2], a[0], a[1])
        if op == "CvtBoolToUint8":
            return z3.If(a[0], self.bv(1, 8), self.bv(0, 8))
        if op in ("Not", "AndB", "OrB", "EqB", "NeqB"):
            return {"Not": lambda: z3.Not(a[0]), "AndB": lambda: z3.And(a[0], a[1]),
                    "OrB": lambda: z3.Or(a[0], a[1]), "EqB": lambda: a[0] == a[1],
                    "NeqB": lambda: a[0] != a[1]}[op]()
        m = re.fullmatch(r"(Trunc|SignExt|ZeroExt)(\d+)to(\d+)", op)
        if m:
            fr, to = int(m.group(2)), int(m.group(3))
            if m.group(1) == "Trunc":
                return z3.Extract(to - 1, 0, a[0])
            return (z3.SignExt if m.group(1) == "SignExt" else z3.ZeroExt)(to - fr, a[0])
        m = re.fullmatch(r"(Add|Sub|Mul|And|Or|Xor)(8|16|32|64)", op)
        if m:
            x, y = a
            return {"Add": x + y, "Sub": x - y, "Mul": x * y, "And": x & y, "Or": x | y, "Xor": x ^ y}[m.group(1)]
        m = re.fullmatch(r"(Com|Neg)(8|16|32|64)", op)
        if m:
            return ~a[0] if m.group(1) == "Com" else -a[0]
        m = re.fullmatch(r"(Div|Mod)(8|16|32|64)(u?)", op)
        if m:
            return self._divmod(v, m.group(1), int(m.group(2)), m.group(3) == "u", *a)
        m = re.fullmatch(r"Hmul(32|64)(u?)", op)
        if m:
            w = int(m.group(1))
            ext = z3.ZeroExt if m.group(2) else z3.SignExt
            return z3.Extract(2 * w - 1, w, ext(w, a[0]) * ext(w, a[1]))
        m = re.fullmatch(r"Avg(32|64)u", op)
        if m:
            w = int(m.group(1))
            self.oblige(v, "Avg arg0 >= arg1", z3.UGE(a[0], a[1]))
            return z3.Extract(w, 1, z3.ZeroExt(1, a[0]) + z3.ZeroExt(1, a[1]))
        m = re.fullmatch(r"(Lsh|Rsh)(8|16|32|64)(U?)x(8|16|32|64)", op)
        if m:
            return self._shift(v, m.group(1), int(m.group(2)), bool(m.group(3)), int(m.group(4)), *a)
        m = re.fullmatch(r"(Eq|Neq|Less|Leq)(8|16|32|64)(U?)", op)
        if m:
            x, y = a
            k, u = m.group(1), bool(m.group(3))
            if k == "Eq":
                return x == y
            if k == "Neq":
                return x != y
            if k == "Less":
                return z3.ULT(x, y) if u else x < y
            return z3.ULE(x, y) if u else x <= y
        m = re.fullmatch(r"(BitLen|Ctz|PopCount|Bswap|BitRev)(8|16|32|64)(NonZero)?", op)
        if m:
            return self._bits(v, m.group(1), int(m.group(2)), bool(m.group(3)), a[0])
        m = re.fullmatch(r"RotateLeft(8|16|32|64)", op)
        if m:
            w = int(m.group(1))
            c = a[1]
            cw = c.size()
            c = z3.Extract(w - 1, 0, c) if cw > w else z3.ZeroExt(w - cw, c)
            return z3.RotateLeft(a[0], z3.URem(c, self.bv(w, w)))
        raise Unsupported(f"op {op}")

    def _phi(self, v):
        b = self.f.block(v.block)
        if len(v.args) != len(b.preds):
            raise Unsupported(f"phi {v.id} arity")
        if not any(p in {blk.name for blk in self.f.blocks} for p in b.preds):
            raise Unsupported(f"phi {v.id} without a live predecessor")
        seen, res = {}, None
        names = {blk.name for blk in self.f.blocks}
        for p, x in zip(b.preds, v.args):
            if p not in names:  # an edge from a block deleted by the pass: never taken
                continue
            k = seen.get(p, 0)
            seen[p] = k + 1
            val = self.enc(x)
            res = val if res is None else z3.If(
                self.edges.get((p, b.name, k), z3.BoolVal(False, self.ctx)), val, res)
        return res

    def _divmod(self, v, kind, w, unsigned, x, y):
        self.oblige(v, "divisor != 0", y != self.bv(0, w))
        if unsigned:
            return z3.UDiv(x, y) if kind == "Div" else z3.URem(x, y)
        if v.auxint == "true":
            self.oblige(v, "not MinInt / -1 ([true])",
                        z3.Or(x != self.bv(1 << (w - 1), w), y != self.bv((1 << w) - 1, w)))
        return x / y if kind == "Div" else z3.SRem(x, y)

    def _shift(self, v, kind, w, unsigned, cw, x, c):
        if c.size() != cw:
            raise Unsupported(f"shift count width of {v.id}")
        big = z3.UGE(c, self.bv(w, cw)) if w < (1 << cw) else z3.BoolVal(False, self.ctx)
        if v.auxint == "true":
            self.oblige(v, "bounded shift count < width ([true])", z3.Not(big))
        n = z3.Extract(w - 1, 0, c) if cw > w else z3.ZeroExt(w - cw, c)
        if kind == "Lsh":
            return z3.If(big, self.bv(0, w), x << n)
        if unsigned:
            return z3.If(big, self.bv(0, w), z3.LShR(x, n))
        return z3.If(big, x >> (w - 1), x >> n)

    def _bits(self, v, kind, w, nonzero, x):
        rw = self._width(v)
        bit = lambda i: z3.Extract(i, i, x) == 1  # noqa: E731
        if kind in ("Bswap", "BitRev"):
            if kind == "Bswap":
                r = z3.Concat(*[z3.Extract(8 * i + 7, 8 * i, x) for i in range(w // 8)])
            else:
                r = z3.Concat(*[z3.Extract(i, i, x) for i in range(w)])
            return r if rw == w else z3.ZeroExt(rw - w, r) if rw > w else z3.Extract(rw - 1, 0, r)
        if nonzero:
            self.oblige(v, f"{kind}NonZero argument != 0", x != self.bv(0, w))
        if kind == "PopCount":
            return sum((z3.ZeroExt(rw - 1, z3.Extract(i, i, x)) for i in range(w)), self.bv(0, rw))
        r = self.bv(w if kind == "Ctz" else 0, rw)
        rng = reversed(range(w)) if kind == "Ctz" else range(w)
        for i in rng:
            r = z3.If(bit(i), self.bv(i if kind == "Ctz" else i + 1, rw), r)
        return r

    # ---- outcome
    def outcome(self):
        """(kind, value): kind 0 = return, i+1 = PANICS[i]; value 64 bits."""
        kind, val = self.bv(len(PANICS) + 1, 8), self.bv(0, 64)  # unreachable default
        for b in self.order:
            if b.kind == "Ret":
                mr = self.f.values[b.controls[0]]
                if mr.op != "MakeResult" or len(mr.args) != 2:
                    raise Unsupported("result shape")
                r = self.enc(mr.args[0])
                if r.size() != 64:
                    raise Unsupported("non-64-bit result")
                kind = z3.If(self.reach[b.name], self.bv(0, 8), kind)
                val = z3.If(self.reach[b.name], r, val)
            elif b.kind == "Exit":
                call = self.f.values[b.controls[0]]
                callee = (call.aux or "").removeprefix("AuxCall{").removesuffix("}")
                if call.op not in ("StaticCall", "StaticLECall") or callee not in PANICS:
                    raise Unsupported(f"exit through {call.op} {callee}")
                kind = z3.If(self.reach[b.name], self.bv(PANICS.index(callee) + 1, 8), kind)
                val = z3.If(self.reach[b.name], self.bv(0, 64), val)
        for b in self.order:  # every value must be encodable, reachable or not
            for v in b.values:
                self.enc(v.id)
        return kind, val


def _encode(f, ctx):
    e = _Enc(f, ctx)
    return e, e.outcome()


def _inputs(model, params):
    return {n: model.eval(p, model_completion=True).as_long() for n, p in params.items()}


def evaluate(f, inputs):
    """('ret', value) or ('panic:<callee>', 0) for concrete parameter values."""
    ctx = z3.Context()
    e, (kind, val) = _encode(f, ctx)
    sub = [(p, z3.BitVecVal(inputs[n], 64, ctx)) for n, p in e.params.items()]
    k = z3.simplify(z3.substitute(kind, *sub)).as_long() if sub else z3.simplify(kind).as_long()
    v = z3.simplify(z3.substitute(val, *sub)).as_long() if sub else z3.simplify(val).as_long()
    if k == 0:
        return ("ret", v)
    if k <= len(PANICS):
        return (f"panic:{PANICS[k - 1]}", 0)
    raise Unsupported("no terminal block reached")


def equivalent(f1, f2, timeout_ms=20000):
    """None if f1 and f2 agree on every input, else a counterexample dict."""
    ctx = z3.Context()
    e1, (k1, v1) = _encode(f1, ctx)
    e2, (k2, v2) = _encode(f2, ctx)
    s = z3.Solver(ctx=ctx)
    s.set(timeout=timeout_ms)
    for n in set(e1.params) ^ set(e2.params):  # a parameter only one side reads
        (e1 if n in e2.params else e2).param(n)
    s.add(z3.Or(k1 != k2, z3.And(k1 == 0, v1 != v2)))
    r = s.check()
    if r == z3.unsat:
        return None
    if r == z3.unknown:
        raise Unsupported("solver timeout")
    return _inputs(s.model(), {**e1.params, **e2.params})


def obligations(f, timeout_ms=20000):
    """Facts claimed by the IR that some input violates."""
    ctx = z3.Context()
    e, _ = _encode(f, ctx)
    out = []
    for v, what, bad in e.obl:
        s = z3.Solver(ctx=ctx)
        s.set(timeout=timeout_ms)
        s.add(bad)
        if s.check() == z3.sat:
            out.append({"value": v.id, "op": v.op, "fact": what, "inputs": _inputs(s.model(), e.params)})
    return out


def op_widths(v):
    """(result width, [(arg id, expected width)]) implied by a sized op, or None."""
    m = re.fullmatch(r"Const(8|16|32|64)", v.op)
    if m:
        return int(m.group(1)), []
    m = re.fullmatch(r"(?:Add|Sub|Mul|And|Or|Xor|Com|Neg|Div|Mod|Hmul|Avg|Bswap|BitRev)(8|16|32|64)u?", v.op)
    if m:
        return int(m.group(1)), [(a, int(m.group(1))) for a in v.args]
    m = re.fullmatch(r"(?:Lsh|Rsh)(8|16|32|64)U?x(8|16|32|64)", v.op)
    if m:
        return int(m.group(1)), [(v.args[0], int(m.group(1))), (v.args[1], int(m.group(2)))]
    m = re.fullmatch(r"(?:Trunc|SignExt|ZeroExt)(\d+)to(\d+)", v.op)
    if m:
        return int(m.group(2)), [(v.args[0], int(m.group(1)))]
    m = re.fullmatch(r"(?:Eq|Neq|Less|Leq)(8|16|32|64)U?", v.op)
    if m:
        return 1, [(a, int(m.group(1))) for a in v.args]
    return None


def ill_typed(f, word_bits=64):
    """Values whose type disagrees with the width their op implies.

    The encoding follows the op (Const64 is 64 bits whatever its type), so a
    pass that builds e.g. Const64 <int32> is not caught by the equivalence
    check, while later passes and the lowering trust the type. word_bits is the
    size of int/uint/uintptr on the target.
    """
    widths = dict(WIDTH, int=word_bits, uint=word_bits, uintptr=word_bits)
    out = []
    for v in f.values.values():
        ow = op_widths(v)
        if ow is None:
            continue
        res, args = ow
        tw = widths.get(v.type)
        if tw not in (None, res):
            out.append({"value": v.id, "op": v.op, "problem": f"type {v.type} for a {res}-bit result",
                        "type_bits": tw, "op_bits": res})
        for a, aw in args:
            atw = widths.get(f.values[a].type) if a in f.values else None
            if atw not in (None, aw):
                out.append({"value": v.id, "op": v.op, "arg": a, "type_bits": atw, "op_bits": aw,
                            "problem": f"argument {a} of type {f.values[a].type} where {aw} bits are expected"})
    return out


def fits_type(f, vid, word_bits=64, timeout_ms=20000):
    """True if value vid always fits its (narrower) type where it is reached.

    gc's rules sometimes give a wide op a narrow type (divmod.rules types the
    32-bit shifts of an int8 division as int8). That is sound when the value is
    the sign- or zero-extension of its low bits, which is what later passes
    assume from the type.
    """
    v = f.values[vid]
    tw = dict(WIDTH, int=word_bits, uint=word_bits, uintptr=word_bits).get(v.type)
    ctx = z3.Context()
    e = _Enc(f, ctx)
    e.outcome()
    val = e.enc(vid)
    if tw is None or not z3.is_bv(val) or tw >= val.size():
        return False
    ext = z3.ZeroExt if v.type.startswith("u") else z3.SignExt
    s = z3.Solver(ctx=ctx)
    s.set(timeout=timeout_ms)
    s.add(e.reach[v.block], ext(val.size() - tw, z3.Extract(tw - 1, 0, val)) != val)
    return s.check() == z3.unsat


def _norm(text):
    return re.sub(r"\((?:[-+]?\d+|\?)\) ", "", text)


def validate(passes, word_bits=64):
    """Check a function's generic passes. passes = [(name, dump text), ...]."""
    rep = {"checked": 0, "failures": [], "unsupported": None, "benign": 0}
    try:
        parsed = [(n, parse_dump(t)) for n, t in passes]
        prev_name, prev, prev_text = None, None, None
        seen_obl = set()
        for (name, f), (_, text) in zip(parsed, passes):
            for o in ill_typed(f, word_bits):
                key = (o["value"], o["problem"])
                if key in seen_obl:
                    continue
                seen_obl.add(key)
                if o.get("type_bits", 99) < o.get("op_bits", 0):
                    try:
                        if fits_type(f, o.get("arg", o["value"]), word_bits):
                            rep["benign"] += 1
                            continue
                    except (Unsupported, z3.Z3Exception):
                        pass
                rep["failures"].append({"kind": "type", "pass": name, **o})
            try:
                obls = obligations(f)
            except z3.Z3Exception as exc:  # mixed widths: only possible in ill-typed IR
                rep["unsupported"] = f"cannot encode {name} (ill-typed IR): {exc}"
                break
            for o in obls:
                key = (o["value"], o["fact"])
                if key not in seen_obl:
                    seen_obl.add(key)
                    rep["failures"].append({"kind": "fact", "pass": name, **o})
            if prev is not None and _norm(text) != _norm(prev_text):
                cex = equivalent(prev, f)
                rep["checked"] += 1
                if cex is not None:
                    rep["failures"].append({"kind": "equivalence", "pass": name, "after": prev_name,
                                            "inputs": cex, "before_out": evaluate(prev, cex),
                                            "after_out": evaluate(f, cex)})
            elif prev is None:
                _encode(f, z3.Context())  # raises Unsupported early
            prev_name, prev, prev_text = name, f, text
    except Unsupported as exc:
        rep["unsupported"] = str(exc)
    return rep


_DUMPDIR = []  # one GOSSADIR per process: a new value rebuilds the whole standard library
_NONCE = [0]


def _dumpdir():
    if not _DUMPDIR:
        _DUMPDIR.append(Path(tempfile.mkdtemp(prefix="ssa_tv_gossadir_")))
    return _DUMPDIR[0]


def dump_passes(go, pkgdir, funcs, goarch=None, extra_env=None):
    """Generic-pass dumps, in pass order, up to (not including) lower.

    funcs is a name (returns [(pass, text), ...]) or a list of names (returns
    {name: [...]}, from a single build). Raises RuntimeError when the build
    produced no dump for a function (e.g. an internal compiler error).
    """
    names = [funcs] if isinstance(funcs, str) else list(funcs)
    out = _dumpdir()
    for p in out.glob("*.dump"):
        p.unlink()
    _NONCE[0] += 1  # a changed package forces the compile (and the dumps) despite the build cache
    (Path(pkgdir) / "zz_ssa_tv_nonce.go").write_text(f"package main\n\n// {os.getpid()} {_NONCE[0]}\n")
    env = dict(os.environ, GOSSADIR=str(out), **(extra_env or {}))
    if goarch:
        env["GOARCH"] = goarch
    flags = ",".join(f"ssa/all/dump={fn}" for fn in names)
    r = subprocess.run([go, "build", f"-gcflags=-d={flags}", "-o", os.devnull, "."],
                       cwd=pkgdir, env=env, capture_output=True, text=True)
    res = {}
    for fn in names:
        files = sorted(out.glob(f"{fn}_*__*.dump"), key=lambda p: int(p.name[len(fn) + 1:].split("__")[0]))
        if not files:
            raise RuntimeError(f"no SSA dump for {fn}: {r.stderr.strip()[:1500]}")
        passes = []
        for p in files:
            name = p.name.split("__", 1)[1][:-len(".dump")]
            if name == "lower":
                break
            passes.append((name, p.read_text()))
        res[fn] = passes
    return res[funcs] if isinstance(funcs, str) else res


def check_source(go, src, funcs=None, goarch=None):
    tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_"))
    try:
        (tmp / "main.go").write_text(src)
        (tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        names = funcs or re.findall(r"^func (v\d+)\(", src, re.M)
        try:
            dumps = dump_passes(go, tmp, names, goarch)
        except RuntimeError:  # one function broke the build: retry them one by one
            dumps = {}
            for fn in names:
                try:
                    dumps[fn] = dump_passes(go, tmp, fn, goarch)
                except RuntimeError as exc:
                    dumps[fn] = exc
        reps = {}
        for fn in names:
            if isinstance(dumps[fn], RuntimeError):
                reps[fn] = {"checked": 0, "failures": [], "unsupported": None, "build_error": str(dumps[fn])[:2000]}
            else:
                reps[fn] = validate(dumps[fn], 32 if goarch in ("386", "arm", "mips", "mipsle") else 64)
        return reps
    finally:
        shutil.rmtree(tmp, ignore_errors=True)


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    for name in ("check", "gen"):
        p = sub.add_parser(name)
        p.add_argument("--go", default=os.environ.get("GO") or shutil.which("go") or "go")
        p.add_argument("--goarch")
        if name == "check":
            p.add_argument("file")
            p.add_argument("--funcs")
        else:
            p.add_argument("--suite", default="core")
            p.add_argument("--seed", type=int, default=1)
            p.add_argument("--start", type=int, default=0)
            p.add_argument("--count", type=int, default=10)
    a = ap.parse_args(argv)
    if a.cmd == "check":
        reps = {a.file: check_source(a.go, Path(a.file).read_text(),
                                     a.funcs.split(",") if a.funcs else None, a.goarch)}
    else:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import alt_compiler_diff as acd
        reps = {}
        for i in range(a.start, a.start + a.count):
            prog = acd.random_program(a.suite, a.seed, i)
            reps[f"{a.suite}-{a.seed}-{i:05d}"] = check_source(a.go, prog.source, goarch=a.goarch)
    total = {"functions": 0, "unsupported": 0, "pairs": 0, "failures": 0}
    for prog, fns in reps.items():
        for fn, r in fns.items():
            total["functions"] += 1
            total["unsupported"] += r["unsupported"] is not None
            if r.get("build_error"):
                total["build_errors"] = total.get("build_errors", 0) + 1
                print(json.dumps({"program": prog, "func": fn, "kind": "build_error",
                                  "error": r["build_error"].splitlines()[1:3]}))
            total["pairs"] += r["checked"]
            for fl in r["failures"]:
                total["failures"] += 1
                print(json.dumps({"program": prog, "func": fn, **fl}, default=str))
    print(json.dumps(total), file=sys.stderr)
    return 1 if total["failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
