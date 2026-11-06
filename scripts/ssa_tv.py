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

Functions with heap memory, loops, calls other than b2i or unmodelled ops are reported
as unsupported and skipped. With --lowered on amd64, ppc64 or ppc64le, the check
goes on through the lowered passes up to regalloc, with the machine semantics of
the target's ops (bits the ISA leaves undefined are free variables). --gcflags
"-N -l" checks debug builds, whose stack slots are modelled byte by byte. The
lowered passes of other architectures are out of scope.

  python3 scripts/ssa_tv.py check main.go [--go GO] [--goarch A] [--funcs v0,v1] [--lowered] [--gcflags F]
  python3 scripts/ssa_tv.py gen --suite core --seed 7 --count 20 [--go GO] [--goarch A] [--lowered]
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
MEM_OPS = {"InitMem", "Copy", "Phi", "InlMark", "StaticCall", "StaticLECall", "CALLstatic", "MakeResult"}
CALLS = ("StaticCall", "StaticLECall", "CALLstatic")
PANICS = ("runtime.panicdivide", "runtime.panicshift", "runtime.panicoverflow")
TIMEOUT_MS = [20000]  # per solver query; --timeout-ms


class Unsupported(Exception):
    """The function uses something this encoding does not model."""


class SolverTimeout(Unsupported):
    """z3 gave up on one query (typically 64x64-bit multiplications)."""


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


LOWERED_ARCHES = ("ppc64", "ppc64le", "amd64")


class Mem:
    """Stack memory as a map (symbol, byte offset) -> 8-bit value."""

    def __init__(self, cells):
        self.cells = cells

    def merge(self, cond, other, enc):
        """cond ? self : other, byte by byte."""
        keys = set(self.cells) | set(other.cells)
        cells = {}
        for k in keys:
            a = self.cells.get(k, None)
            b = other.cells.get(k, None)
            a = a if a is not None else enc._byte0(k)
            b = b if b is not None else enc._byte0(k)
            cells[k] = z3.If(cond, a, b)
        return Mem(cells)


X86_CONDS = {"EQ", "NE", "LT", "LE", "GT", "GE", "ULT", "ULE", "UGT", "UGE"}
X86_SET = {"EQ": "EQ", "NE": "NE", "L": "LT", "LE": "LE", "G": "GT", "GE": "GE",
           "B": "ULT", "BE": "ULE", "A": "UGT", "AE": "UGE"}
X86_CMOV = {"EQ": "EQ", "NE": "NE", "LT": "LT", "GT": "GT", "LE": "LE", "GE": "GE",
            "HI": "UGT", "CC": "UGE", "CS": "ULT", "LS": "ULE"}
AMD64_MEM_OPS = {"MOVBstore", "MOVWstore", "MOVLstore", "MOVQstore", "MOVBstoreconst", "MOVWstoreconst",
                 "MOVLstoreconst", "MOVQstoreconst"}
AMD64_OPS = AMD64_MEM_OPS | {
    "MOVBload", "MOVWload", "MOVLload", "MOVQload", "MOVBQSXload", "MOVWQSXload", "MOVLQSXload",
    "MOVQconst", "MOVLconst", "MOVBQSX", "MOVBQZX", "MOVWQSX", "MOVWQZX", "MOVLQSX", "MOVLQZX",
    "NEGQ", "NEGL", "NOTQ", "NOTL", "SBBQcarrymask", "SBBLcarrymask", "HMULQ", "HMULQU", "HMULL", "HMULLU",
    "AVGQU", "BSFQ", "BSFL", "BSRQ", "BSRL", "BSFQinit", "BSRQinit", "POPCNTQ", "POPCNTL", "BSWAPQ",
    "BSWAPL", "LoweredHasCPUFeature", "Select0", "Select1"}
AMD64_OPS |= {f"{o}{w}{s}" for o in ("ADD", "SUB", "AND", "OR", "XOR", "MUL") for w in "QL" for s in ("", "const", "load")}
AMD64_OPS |= {f"{o}{w}{s}" for o in ("SHL", "SHR", "SAR", "ROL", "ROR") for w in "QLWB" for s in ("", "const")}
AMD64_OPS |= {f"LEA{w}{s}" for w in "QL" for s in ("", "1", "2", "4", "8")}
AMD64_OPS |= {f"BT{k}{w}const" for k in "RSC" for w in "QL"}
AMD64_OPS |= {f"SET{c}" for c in X86_SET} | {f"CMOV{w}{c}" for w in "QLW" for c in X86_CMOV}
AMD64_OPS |= {f"{k}{w}{c}{l}" for k in ("CMP", "TEST") for w in "QLWB" for c in ("", "const") for l in ("", "load")}
AMD64_OPS |= {f"DIV{w}{u}" for w in "QLW" for u in ("", "U")}


def _xcond(cond, flags):
    """x86 condition on a (slt, ult, eq) flags triple."""
    if not (isinstance(flags, tuple) and flags[0] == "xflags"):
        raise Unsupported("condition on a non-flags value")
    _, slt, ult, eq = flags
    return {"EQ": eq, "NE": z3.Not(eq), "LT": slt, "LE": z3.Or(slt, eq), "GT": z3.Not(z3.Or(slt, eq)),
            "GE": z3.Not(slt), "ULT": ult, "ULE": z3.Or(ult, eq), "UGT": z3.Not(z3.Or(ult, eq)),
            "UGE": z3.Not(ult)}[cond]


FLAG_BLOCKS = {"LT": 0, "GT": 1, "EQ": 2, "GE": 4, "LE": 5, "NE": 6}  # ppc64 CR-bit codes
PPC64_OPS = {
    "MOVBreg", "MOVBZreg", "MOVHreg", "MOVHZreg", "MOVWreg", "MOVWZreg", "MOVDconst", "ADD", "SUB", "AND", "OR",
    "XOR", "NOR", "ANDN", "ORN", "EQV", "NEG", "MULLD", "ADDconst", "ANDconst", "ORconst", "XORconst",
    "SUBFCconst", "MULLDconst", "MULLWconst", "MULLW", "MULHD", "MULHDU", "SLDconst", "SRDconst", "SRADconst",
    "SLWconst", "SRWconst", "SRAWconst", "ROTLconst", "ROTLWconst", "CNTLZD", "POPCNTD", "POPCNTW", "POPCNTB",
    "SLD", "SRD", "SRAD", "SLW", "SRW", "SRAW", "ROTL", "ROTLW", "RLDICL", "RLDICR", "RLWINM", "CLRLSLDI",
    "CLRLSLWI", "DIVD", "DIVDU", "DIVW", "DIVWU", "CMP", "CMPU", "CMPW", "CMPWU", "CMPconst", "CMPUconst",
    "CMPWconst", "CMPWUconst", "ADDCC", "ANDCC", "ORCC", "XORCC", "NORCC", "ANDNCC", "SUBCC", "ANDCCconst",
    "Select0", "Select1", "ISEL", "ISELZ", "SETBC", "SETBCR", "MODSD", "MODUD", "MODSW", "MODUW", "CNTTZD",
    "CNTTZW", "CNTLZW", "BRD", "BRW", "BRH"}


def _flags(l, r, signed):
    """A ppc64 condition-register field: (lt, gt, eq)."""
    if signed:
        return ("flags", l < r, l > r, l == r)
    return ("flags", z3.ULT(l, r), z3.UGT(l, r), l == r)


def _cond(code, flags):
    """CR-bit test of ISEL/SETBC and branch blocks: 0 LT, 1 GT, 2 EQ; +4 negates."""
    if not (isinstance(flags, tuple) and flags[0] == "flags"):
        raise Unsupported("condition on a non-flags value")
    bit = flags[1 + (code & 3)]
    return z3.Not(bit) if code & 4 else bit


def _ppc64_rotmask(aux):
    """DecodePPC64RotateMask (rewrite.go): rotate, mask, nbits."""
    aux &= M64
    rot, mb, me, nbits = (aux >> 16) & 0xFF, (aux >> 8) & 0xFF, aux & 0xFF, (aux >> 24) & 0xFF
    mask = ((1 << (nbits - mb)) - 1) ^ ((1 << (nbits - me)) - 1)
    if mb > me:
        mask = ~mask & M64
    if nbits == 32:
        mask &= 0xFFFFFFFF
    return rot, mask & M64, nbits


class _Enc:
    """z3 encoding of one parsed function, in its own context."""

    def __init__(self, f, ctx):
        self.f, self.ctx, self.cache, self.obl = f, ctx, {}, []
        self.params = {}
        self.arch = getattr(f, "arch", None)
        self.lowered = self.arch in LOWERED_ARCHES
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
        elif self.arch == "amd64" and b.kind in X86_CONDS:
            c = _xcond(b.kind, self.enc(b.controls[0]))
            outs = [z3.And(r, c), z3.And(r, z3.Not(c))]
        elif b.kind in FLAG_BLOCKS and self.lowered:
            c = _cond(FLAG_BLOCKS[b.kind], self.enc(b.controls[0]))
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
        if op in ("InitMem",):
            return Mem({})
        if op in ("MakeResult", "InlMark", "VarDef", "VarLive", "VarKill"):
            return a[-1] if op != "MakeResult" else None
        if op in CALLS:
            return self._call(v, a)
        if op == "SelectN":
            if not (isinstance(a[0], tuple) and a[0][0] == "call"):
                raise Unsupported("SelectN of a non-call")
            return a[0][1 + int(v.auxint)]
        if op in ("SP", "LocalAddr", "OffPtr", "Store", "Load", "Dereference") and not self.lowered or op == "SP":
            return self._generic_mem(v, a)
        if v.type == "mem" and op not in ("Copy", "Phi") and not (self.lowered and op in AMD64_MEM_OPS):
            raise Unsupported(f"memory op {op}")
        if op == "HasCPUFeature":
            return z3.Bool(f"cpu_{v.aux}", self.ctx)
        if self.arch == "amd64" and op in AMD64_OPS:
            return self._amd64(v, a)
        if self.lowered and self.arch != "amd64" and op in PPC64_OPS:
            return self._ppc64(v, a)
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
            cond = self.edges.get((p, b.name, k), z3.BoolVal(False, self.ctx))
            if isinstance(val, Mem):
                res = val if res is None else val.merge(cond, res, self)
            elif isinstance(val, tuple):
                raise Unsupported(f"phi {v.id} of flags or tuples")
            else:
                res = val if res is None else z3.If(cond, val, res)
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

    # ---- memory (stack slots of -N code) and calls
    def _byte0(self, key):
        """Initial content of a stack byte: shared by name across passes."""
        return z3.BitVec(f"stk_{key[0]}_{key[1]}", 8, self.ctx)

    def _read(self, mem, sym, off, nbytes):
        cells = [mem.cells.get((sym, off + i)) for i in range(nbytes)]
        cells = [c if c is not None else self._byte0((sym, off + i)) for i, c in enumerate(cells)]
        return z3.Concat(*reversed(cells)) if nbytes > 1 else cells[0]  # little endian

    def _write(self, mem, sym, off, val, nbytes):
        cells = dict(mem.cells)
        for i in range(nbytes):
            cells[(sym, off + i)] = z3.Extract(8 * i + 7, 8 * i, val)
        return Mem(cells)

    def _generic_mem(self, v, a):
        op = v.op
        if op == "SP":
            return ("ptr", None, 0)
        if op == "LocalAddr":
            return ("ptr", v.aux, 0)
        if op == "OffPtr":
            if not (isinstance(a[0], tuple) and a[0][0] == "ptr"):
                raise Unsupported("OffPtr of a non-pointer")
            return ("ptr", a[0][1], a[0][2] + int(v.auxint))
        ptr = a[0]
        if not (isinstance(ptr, tuple) and ptr[0] == "ptr" and ptr[1] is not None):
            raise Unsupported(f"{op} through an unknown pointer")
        if op == "Store":
            typ, val, mem = v.aux, a[1], a[2]
            if typ == "bool":
                val = z3.If(val, self.bv(1, 8), self.bv(0, 8))
            if typ not in WIDTH:
                raise Unsupported(f"store of {typ}")
            nb = max(WIDTH[typ], 8) // 8
            return self._write(mem, ptr[1], ptr[2], val, nb)
        typ, mem = v.type, a[1]  # Load, Dereference
        if typ not in WIDTH:
            raise Unsupported(f"load of {typ}")
        val = self._read(mem, ptr[1], ptr[2], max(WIDTH[typ], 8) // 8)
        return val != self.bv(0, 8) if typ == "bool" else val

    def _call(self, v, a):
        callee = (v.aux or "").removeprefix("AuxCall{").removesuffix("}")
        mem = next((x for x in reversed(a) if isinstance(x, Mem)), None)
        if callee in PANICS:
            return mem
        if callee == "main.b2i" and len(a) >= 2:
            arg = a[0]
            t = arg if z3.is_bool(arg) else z3.Extract(7, 0, arg) != self.bv(0, 8)
            return ("call", z3.If(t, self.bv(1, 64), self.bv(0, 64)), mem)
        raise Unsupported(f"call to {callee}")

    # ---- amd64 (lowered passes): every value is a 64-bit register
    def _amd64(self, v, a):
        op, aux, bv = v.op, v.auxint, self.bv
        x = a[0] if a else None
        y = a[1] if len(a) > 1 else None
        lo = lambda w, val: z3.Extract(w - 1, 0, val)  # noqa: E731
        zx = lambda w, r: z3.ZeroExt(64 - w, r) if w < 64 else r  # noqa: E731
        part = lambda w, old, r: z3.Concat(z3.Extract(63, w, old), r) if w < 64 else r  # noqa: E731
        # a w-bit result: 64 as is, 32 zero-extends (x86-64), 8/16 keep the destination's upper bits
        put = lambda w, dst, r: r if w == 64 else zx(32, r) if w == 32 else part(w, dst, r)  # noqa: E731
        W = {"Q": 64, "L": 32, "W": 16, "B": 8}

        def c_imm(w):
            return bv(int(aux) & ((1 << w) - 1), w)

        m = re.fullmatch(r"(ADD|SUB|AND|OR|XOR|MUL)(Q|L)(const|load)?", op)
        if m and op not in ("MULQload",):
            w = W[m.group(2)]
            if m.group(3) == "load":
                rhs = self._read(a[2], *self._x86_addr(v, a[1]), w // 8)
            else:
                rhs = c_imm(w) if m.group(3) == "const" else lo(w, y)
            l = lo(w, x)
            r = {"ADD": l + rhs, "SUB": l - rhs, "AND": l & rhs, "OR": l | rhs, "XOR": l ^ rhs, "MUL": l * rhs}[m.group(1)]
            return put(w, x, r)
        m = re.fullmatch(r"(NEG|NOT)(Q|L)", op)
        if m:
            w = W[m.group(2)]
            return put(w, x, -lo(w, x) if m.group(1) == "NEG" else ~lo(w, x))
        m = re.fullmatch(r"(SHL|SHR|SAR|ROL|ROR)(Q|L|W|B)(const)?", op)
        if m:
            return self._x86_shift(m.group(1), W[m.group(2)], x, y if not m.group(3) else None, aux)
        m = re.fullmatch(r"MOV(Q|L)const", op)
        if m:
            return bv(int(aux) & ((1 << W[m.group(1)]) - 1), 64)
        m = re.fullmatch(r"MOV(B|W|L)Q(SX|ZX)", op)
        if m:
            w = W[m.group(1)]
            return (z3.SignExt if m.group(2) == "SX" else z3.ZeroExt)(64 - w, lo(w, x))
        m = re.fullmatch(r"LEA(Q|L)([1248])?", op)
        if m:
            if v.aux:
                raise Unsupported(f"{op} of a symbol")
            off = int(aux or 0) & M64
            r = x + (y * bv(int(m.group(2)), 64) if m.group(2) else bv(0, 64)) + bv(off, 64)
            return r if m.group(1) == "Q" else zx(32, lo(32, r))
        m = re.fullmatch(r"BT(R|S|C)(Q|L)const", op)
        if m:
            w = W[m.group(2)]
            bit = bv(1 << int(aux), w)
            l = lo(w, x)
            r = {"R": l & ~bit, "S": l | bit, "C": l ^ bit}[m.group(1)]
            return put(w, x, r)
        m = re.fullmatch(r"SBB(Q|L)carrymask", op)
        if m:
            w = W[m.group(1)]
            return zx(w, z3.If(x[2], bv((1 << w) - 1, w), bv(0, w)))
        m = re.fullmatch(r"SET(EQ|NE|L|LE|G|GE|B|BE|A|AE)", op)
        if m:
            c = _xcond(X86_SET[m.group(1)], x)
            return z3.Concat(z3.Extract(63, 8, self._undef(v, 64)), z3.If(c, bv(1, 8), bv(0, 8)))
        m = re.fullmatch(r"CMOV(Q|L|W)(EQ|NE|LT|GT|LE|GE|HI|CC|CS|LS)", op)
        if m:
            w = W[m.group(1)]
            c = _xcond(X86_CMOV[m.group(2)], a[2])
            r = z3.If(c, lo(w, y), lo(w, x))
            return put(w, x, r)
        m = re.fullmatch(r"(CMP|TEST)(Q|L|W|B)(const)?(load)?", op)
        if m:
            return self._x86_cmp(v, m.group(1), W[m.group(2)], bool(m.group(3)), bool(m.group(4)), a)
        m = re.fullmatch(r"DIV(Q|L|W)(U?)", op)
        if m:
            return self._x86_div(v, W[m.group(1)], bool(m.group(2)), x, y)
        if op in ("HMULQ", "HMULQU", "HMULL", "HMULLU"):
            w = 64 if op.startswith("HMULQ") else 32
            ext = z3.ZeroExt if op.endswith("U") else z3.SignExt
            r = z3.Extract(2 * w - 1, w, ext(w, lo(w, x)) * ext(w, lo(w, y)))
            return zx(w, r)
        if op == "AVGQU":
            return z3.Extract(64, 1, z3.ZeroExt(1, x) + z3.ZeroExt(1, y))
        if op in ("BSFQ", "BSFL", "BSRQ", "BSRL"):
            w = 64 if op[-1] == "Q" else 32
            val = lo(w, x)
            idx = self._index_of(val, w, op.startswith("BSF"))
            r = z3.If(val == bv(0, w), self._undef(v, 64), idx)
            if v.type.endswith(",flags"):  # (result, flags): ZF says the source was zero
                free = lambda n: z3.Bool(f"undef_{v.id}_{n}", self.ctx)  # noqa: E731
                return ("tuple", r, ("xflags", free("sf"), free("cf"), val == bv(0, w)))
            return r
        if op in ("BSFQinit", "BSRQinit"):
            idx = self._index_of(y, 64, op.startswith("BSF"))
            return z3.If(y == bv(0, 64), x, idx)
        if op in ("POPCNTQ", "POPCNTL"):
            w = 64 if op[-1] == "Q" else 32
            return sum((z3.ZeroExt(63, z3.Extract(i, i, x)) for i in range(w)), bv(0, 64))
        if op in ("BSWAPQ", "BSWAPL"):
            w = 64 if op[-1] == "Q" else 32
            r = z3.Concat(*[z3.Extract(8 * i + 7, 8 * i, x) for i in range(w // 8)])
            return zx(w, r)
        if op == "LoweredHasCPUFeature":
            return z3.If(z3.Bool(f"cpu_{v.aux}", self.ctx), bv(1, 64), bv(0, 64))
        if op in ("Select0", "Select1"):
            if not (isinstance(x, tuple) and x[0] == "tuple"):
                raise Unsupported(f"{op} of a non-tuple")
            return x[1] if op == "Select0" else x[2]
        m = re.fullmatch(r"MOV(B|W|L|Q)(load|QSXload|store|storeconst)", op)
        if m:
            return self._x86_mem(v, W[m.group(1)], m.group(2), a)
        raise Unsupported(f"amd64 op {op}")

    def _x86_addr(self, v, ptr):
        """(sym, off) of a stack access: SP plus the op's symbol and offset."""
        if not (isinstance(ptr, tuple) and ptr[0] == "ptr" and ptr[1] is None and ptr[2] == 0):
            raise Unsupported(f"{v.op} through a non-SP base")
        if not v.aux:
            raise Unsupported(f"{v.op} without a symbol")
        off = v.auxint or "0"
        if off.startswith("val="):
            off = off.split("off=")[1]
        return v.aux, int(off)

    def _x86_mem(self, v, w, kind, a):
        nb = w // 8
        sym, off = self._x86_addr(v, a[0])
        if kind == "store":
            return self._write(a[2], sym, off, z3.Extract(w - 1, 0, a[1]), nb)
        if kind == "storeconst":
            val = int(v.auxint.split(",")[0].removeprefix("val="))
            return self._write(a[1], sym, off, self.bv(val & ((1 << w) - 1), w), nb)
        r = self._read(a[1], sym, off, nb)
        if kind == "QSXload":
            return z3.SignExt(64 - w, r)
        return z3.ZeroExt(64 - w, r) if w < 64 else r  # MOVBLZX/MOVWLZX/MOVL zero-extend

    def _x86_cmp(self, v, kind, w, const, load, a):
        if load:
            l = self._read(a[-1], *self._x86_addr(v, a[0]), w // 8)
            if const:
                val = int(v.auxint.split(",")[0].removeprefix("val="))
                r = self.bv(val & ((1 << w) - 1), w)
            else:
                r = z3.Extract(w - 1, 0, a[1])
        else:
            l = z3.Extract(w - 1, 0, a[0])
            r = self.bv(int(v.auxint) & ((1 << w) - 1), w) if const else z3.Extract(w - 1, 0, a[1])
        if kind == "CMP":
            return ("xflags", l < r, z3.ULT(l, r), l == r)
        t = l & r
        return ("xflags", t < self.bv(0, w), z3.BoolVal(False, self.ctx), t == self.bv(0, w))

    def _x86_shift(self, kind, w, x, y, aux):
        bv = self.bv
        val = z3.Extract(w - 1, 0, x)
        mask = 63 if w == 64 else 31  # x86 masks the count to 6 bits (64-bit) or 5 bits
        if y is None:
            n = int(aux) & mask
            cnt = bv(n, w) if n < (1 << w) else None
            big = n >= w
        else:
            c = z3.Extract(7, 0, y) & bv(mask, 8)
            cnt = z3.ZeroExt(w - 8, c) if w > 8 else c
            big = z3.UGE(c, bv(w, 8)) if w < 32 else z3.BoolVal(False, self.ctx)
        if kind in ("ROL", "ROR"):
            if y is None:
                k = int(aux) % w
                r = z3.RotateLeft(val, bv(k, w)) if kind == "ROL" else z3.RotateRight(val, bv(k, w))
            else:
                k = z3.URem(cnt, bv(w, w))
                r = z3.RotateLeft(val, k) if kind == "ROL" else z3.RotateRight(val, k)
        elif y is None:
            if kind == "SHL":
                r = bv(0, w) if big else val << bv(n, w)
            elif kind == "SHR":
                r = bv(0, w) if big else z3.LShR(val, bv(n, w))
            else:
                r = val >> bv(min(n, w - 1), w)
        else:
            if kind == "SHL":
                r = z3.If(big, bv(0, w), val << cnt)
            elif kind == "SHR":
                r = z3.If(big, bv(0, w), z3.LShR(val, cnt))
            else:
                r = z3.If(big, val >> bv(w - 1, w), val >> cnt)
        if w == 64:
            return r
        if w == 32:
            return z3.ZeroExt(32, r)
        return z3.Concat(z3.Extract(63, w, x), r)

    def _x86_div(self, v, w, unsigned, x, y):
        bv = self.bv
        xs, ys = z3.Extract(w - 1, 0, x), z3.Extract(w - 1, 0, y)
        undef = z3.Extract(w - 1, 0, self._undef(v, 64))
        if unsigned:
            bad = ys == bv(0, w)
            q, r = z3.UDiv(xs, ys), z3.URem(xs, ys)
        else:
            bad = z3.Or(ys == bv(0, w), z3.And(xs == bv(1 << (w - 1), w), ys == bv((1 << w) - 1, w)))
            q, r = xs / ys, z3.SRem(xs, ys)
        q, r = z3.If(bad, undef, q), z3.If(bad, undef, r)
        if not unsigned and v.auxint != "true":  # DivisionNeedsFixUp: CMP $-1; NEG AX; XORL DX, DX
            m1 = ys == bv((1 << w) - 1, w)
            q, r = z3.If(m1, -xs, q), z3.If(m1, bv(0, w), r)
        if w == 64:
            return ("tuple", q, r)
        if w == 32:
            return ("tuple", z3.ZeroExt(32, q), z3.ZeroExt(32, r))
        hi = z3.Extract(63, w, self._undef(v, 64))  # 16-bit results: upper bits not specified here
        return ("tuple", z3.Concat(hi, q), z3.Concat(hi, r))

    def _index_of(self, val, w, lowest):
        r = self.bv(0, 64)
        rng = reversed(range(w)) if lowest else range(w)
        for i in rng:
            r = z3.If(z3.Extract(i, i, val) == 1, self.bv(i, 64), r)
        return r

    # ---- ppc64 (lowered passes): every value is a 64-bit register
    def _undef(self, v, w):
        """Bits the ISA leaves undefined: free, so any dependence on them shows."""
        return z3.BitVec(f"undef_{v.id}_{w}", w, self.ctx)

    def _ppc64(self, v, a):
        op, aux = v.op, v.auxint
        c = (int(aux) & M64) if aux not in (None, "true", "false") else 0
        bv, lo = self.bv, (lambda x: z3.Extract(31, 0, x))
        sx32, zx32 = (lambda x: z3.SignExt(32, x)), (lambda x: z3.ZeroExt(32, x))
        x = a[0] if a else None
        y = a[1] if len(a) > 1 else None
        ext = {"MOVBreg": (8, True), "MOVBZreg": (8, False), "MOVHreg": (16, True), "MOVHZreg": (16, False),
               "MOVWreg": (32, True), "MOVWZreg": (32, False)}
        if op in ext:
            w, sg = ext[op]
            return (z3.SignExt if sg else z3.ZeroExt)(64 - w, z3.Extract(w - 1, 0, x))
        if op == "MOVDconst":
            return bv(c, 64)
        simple = {"ADD": lambda: x + y, "SUB": lambda: x - y, "AND": lambda: x & y, "OR": lambda: x | y,
                  "XOR": lambda: x ^ y, "NOR": lambda: ~(x | y), "ANDN": lambda: x & ~y, "ORN": lambda: x | ~y,
                  "EQV": lambda: ~(x ^ y), "NEG": lambda: -x, "MULLD": lambda: x * y,
                  "ADDconst": lambda: x + bv(c, 64), "ANDconst": lambda: x & bv(c, 64),
                  "ORconst": lambda: x | bv(c, 64), "XORconst": lambda: x ^ bv(c, 64),
                  "SUBFCconst": lambda: bv(c, 64) - x, "MULLDconst": lambda: x * bv(c, 64),
                  "MULLWconst": lambda: x * bv(c, 64),  # mulli: full 64-bit RA
                  "MULLW": lambda: sx32(lo(x)) * sx32(lo(y)),
                  "MULHD": lambda: z3.Extract(127, 64, z3.SignExt(64, x) * z3.SignExt(64, y)),
                  "MULHDU": lambda: z3.Extract(127, 64, z3.ZeroExt(64, x) * z3.ZeroExt(64, y)),
                  "SLDconst": lambda: x << bv(c, 64), "SRDconst": lambda: z3.LShR(x, bv(c, 64)),
                  "SRADconst": lambda: x >> bv(c, 64),
                  "SLWconst": lambda: zx32(lo(x) << bv(c, 32)), "SRWconst": lambda: zx32(z3.LShR(lo(x), bv(c, 32))),
                  "SRAWconst": lambda: sx32(lo(x) >> bv(c, 32)),
                  "ROTLconst": lambda: z3.RotateLeft(x, bv(c % 64, 64)),
                  "ROTLWconst": lambda: zx32(z3.RotateLeft(lo(x), bv(c % 32, 32))),
                  "CNTLZD": lambda: self._bits_of("BitLen", 64, x, inv=True),
                  "POPCNTD": lambda: sum((z3.ZeroExt(63, z3.Extract(i, i, x)) for i in range(64)), bv(0, 64)),
                  "POPCNTW": lambda: z3.Concat(*[z3.ZeroExt(26, sum((z3.ZeroExt(5, z3.Extract(32 * k + i, 32 * k + i, x))
                                                                     for i in range(32)), bv(0, 6)))
                                                 for k in (1, 0)]),
                  "POPCNTB": lambda: z3.Concat(*[z3.ZeroExt(4, sum((z3.ZeroExt(3, z3.Extract(8 * k + i, 8 * k + i, x))
                                                                    for i in range(8)), bv(0, 4)))
                                                 for k in reversed(range(8))])}
        if op in simple:
            return simple[op]()
        if op in ("SLD", "SRD", "SRAD"):
            n = y & bv(127, 64)
            big = z3.UGE(n, bv(64, 64))
            if op == "SLD":
                return z3.If(big, bv(0, 64), x << n)
            if op == "SRD":
                return z3.If(big, bv(0, 64), z3.LShR(x, n))
            return z3.If(big, x >> 63, x >> n)
        if op in ("SLW", "SRW", "SRAW"):
            n = lo(y) & bv(63, 32)
            big = z3.UGE(n, bv(32, 32))
            if op == "SLW":
                return z3.If(big, bv(0, 64), zx32(lo(x) << n))
            if op == "SRW":
                return z3.If(big, bv(0, 64), zx32(z3.LShR(lo(x), n)))
            return z3.If(big, sx32(lo(x) >> 31), sx32(lo(x) >> n))
        if op in ("ROTL", "ROTLW"):
            if op == "ROTL":
                return z3.RotateLeft(x, y & bv(63, 64))
            return zx32(z3.RotateLeft(lo(x), lo(y) & bv(31, 32)))
        if op in ("RLDICL", "RLDICR", "RLWINM"):
            rot, mask, nbits = _ppc64_rotmask(int(aux))
            if nbits == 32:
                return zx32(z3.RotateLeft(lo(x), bv(rot, 32))) & bv(mask, 64)
            return z3.RotateLeft(x, bv(rot, 64)) & bv(mask, 64)
        if op in ("CLRLSLDI", "CLRLSLWI"):
            mb, sh = (int(aux) >> 8) & 0xFF, (int(aux) >> 16) & 0xFF
            if op == "CLRLSLDI":
                return (x & bv((1 << (64 - mb)) - 1, 64)) << bv(sh, 64)
            return zx32((lo(x) & bv((1 << (32 - mb)) - 1, 32)) << bv(sh, 32))
        if op in ("DIVD", "DIVDU", "DIVW", "DIVWU"):
            return self._ppc64_div(v, op, x, y)
        if op in ("MODSD", "MODUD", "MODSW", "MODUW"):
            return self._ppc64_mod(v, op, x, y)
        if op in ("CNTTZD", "CNTTZW", "CNTLZW"):
            w = 64 if op == "CNTTZD" else 32
            xv = x if w == 64 else lo(x)
            if op == "CNTLZW":
                r = bv(0, 64)
                for i in range(32):
                    r = z3.If(z3.Extract(i, i, xv) == 1, bv(31 - i, 64), r)
                return z3.If(xv == bv(0, 32), bv(32, 64), r)
            r = bv(w, 64)
            for i in reversed(range(w)):
                r = z3.If(z3.Extract(i, i, xv) == 1, bv(i, 64), r)
            return r
        if op in ("BRD", "BRW", "BRH"):
            unit = {"BRD": 64, "BRW": 32, "BRH": 16}[op]
            parts = []
            for k in reversed(range(64 // unit)):  # each unit byte-reversed in place
                u = z3.Extract(unit * k + unit - 1, unit * k, x)
                parts.append(z3.Concat(*[z3.Extract(8 * i + 7, 8 * i, u) for i in range(unit // 8)]))
            return z3.Concat(*parts) if len(parts) > 1 else parts[0]
        cmps = {"CMP": (64, True), "CMPU": (64, False), "CMPW": (32, True), "CMPWU": (32, False)}
        if op in cmps or op[:-5] in cmps and op.endswith("const"):
            w, sg = cmps[op] if op in cmps else cmps[op[:-5]]
            l = x if w == 64 else lo(x)
            r = (y if w == 64 else lo(y)) if op in cmps else bv(c & ((1 << w) - 1), w)
            return _flags(l, r, sg)
        cc = {"ADDCC": lambda: x + y, "ANDCC": lambda: x & y, "ORCC": lambda: x | y, "XORCC": lambda: x ^ y,
              "NORCC": lambda: ~(x | y), "ANDNCC": lambda: x & ~y, "SUBCC": lambda: x - y,
              "ANDCCconst": lambda: x & bv(c, 64)}
        if op in cc:
            val = cc[op]()
            return ("tuple", val, _flags(val, bv(0, 64), True))
        if op in ("Select0", "Select1"):
            if not (isinstance(x, tuple) and x[0] == "tuple"):
                raise Unsupported(f"{op} of a non-tuple")
            return x[1] if op == "Select0" else x[2]
        if op in ("ISEL", "ISELZ"):
            k = int(aux)
            if k & 3 == 3:
                raise Unsupported("ISEL on SO")
            flags = a[2] if op == "ISEL" else a[1]
            other = a[1] if op == "ISEL" else bv(0, 64)
            return z3.If(_cond(k, flags), x, other)
        if op in ("SETBC", "SETBCR"):
            k = int(aux)
            t = _cond(k, x)
            return z3.If(t if op == "SETBC" else z3.Not(t), bv(1, 64), bv(0, 64))
        raise Unsupported(f"ppc64 op {op}")

    def _bits_of(self, kind, w, x, inv=False):
        r = self.bv(0, 64)
        for i in range(w):
            r = z3.If(z3.Extract(i, i, x) == 1, self.bv(i + 1, 64), r)
        return self.bv(w, 64) - r if inv else r

    def _ppc64_mod(self, v, op, x, y):
        """modsd/modud/modsw/moduw (POWER9+). The ISA leaves MinInt % -1 undefined and
        gc emits no fix-up; it relies on the hardware giving 0 (qemu does too), and so
        does this model. A zero divisor is guarded by the IR and left undefined."""
        bv = self.bv
        if op in ("MODSD", "MODUD"):
            if op == "MODUD":
                return z3.If(y == bv(0, 64), self._undef(v, 64), z3.URem(x, y))
            return z3.If(y == bv(0, 64), self._undef(v, 64),
                         z3.If(y == bv(M64, 64), bv(0, 64), z3.SRem(x, y)))
        x32, y32 = z3.Extract(31, 0, x), z3.Extract(31, 0, y)
        hi = z3.Extract(63, 32, self._undef(v, 64))  # RT[0:31] undefined
        if op == "MODUW":
            return z3.If(y32 == bv(0, 32), self._undef(v, 64), z3.Concat(hi, z3.URem(x32, y32)))
        r = z3.If(y32 == bv(0xFFFFFFFF, 32), bv(0, 32), z3.SRem(x32, y32))
        return z3.If(y32 == bv(0, 32), self._undef(v, 64), z3.Concat(hi, r))

    def _ppc64_div(self, v, op, x, y):
        bv = self.bv
        if op in ("DIVD", "DIVDU"):
            if op == "DIVDU":
                return z3.If(y == bv(0, 64), self._undef(v, 64), z3.UDiv(x, y))
            bad = z3.Or(y == bv(0, 64), z3.And(x == bv(1 << 63, 64), y == bv(M64, 64)))
            q = z3.If(bad, self._undef(v, 64), x / y)
            # DivisionNeedsFixUp (AuxInt 0): the backend emits CMP y,$-1 / NEG x.
            return q if v.auxint == "true" else z3.If(y == bv(M64, 64), -x, q)
        x32, y32 = z3.Extract(31, 0, x), z3.Extract(31, 0, y)
        hi = z3.Extract(63, 32, self._undef(v, 64))  # divw/divwu leave RT[0:31] undefined
        if op == "DIVWU":
            return z3.If(y32 == bv(0, 32), self._undef(v, 64), z3.Concat(hi, z3.UDiv(x32, y32)))
        bad = z3.Or(y32 == bv(0, 32), z3.And(x32 == bv(1 << 31, 32), y32 == bv(0xFFFFFFFF, 32)))
        q = z3.If(bad, self._undef(v, 64), z3.Concat(hi, x32 / y32))
        return q if v.auxint == "true" else z3.If(y32 == bv(0xFFFFFFFF, 32), -x, q)

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
                if call.op not in CALLS or callee not in PANICS:
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
    s = z3.Solver(ctx=ctx)
    for n, p in e.params.items():
        s.add(p == z3.BitVecVal(inputs[n], 64, ctx))
    if s.check() != z3.sat:
        raise Unsupported("inconsistent evaluation")
    m = s.model()  # bits the ISA leaves undefined get an arbitrary value
    k = m.eval(kind, model_completion=True).as_long()
    v = m.eval(val, model_completion=True).as_long()
    if k == 0:
        return ("ret", v)
    if k <= len(PANICS):
        return (f"panic:{PANICS[k - 1]}", 0)
    raise Unsupported("no terminal block reached")


def equivalent(f1, f2, timeout_ms=None):
    """None if f1 and f2 agree on every input, else a counterexample dict."""
    ctx = z3.Context()
    e1, (k1, v1) = _encode(f1, ctx)
    e2, (k2, v2) = _encode(f2, ctx)
    s = z3.Solver(ctx=ctx)
    s.set(timeout=timeout_ms or TIMEOUT_MS[0])
    for n in set(e1.params) ^ set(e2.params):  # a parameter only one side reads
        (e1 if n in e2.params else e2).param(n)
    s.add(z3.Or(k1 != k2, z3.And(k1 == 0, v1 != v2)))
    r = s.check()
    if r == z3.unsat:
        return None
    if r == z3.unknown:
        raise SolverTimeout("solver timeout")
    return _inputs(s.model(), {**e1.params, **e2.params})


def obligations(f, timeout_ms=None):
    """Facts claimed by the IR that some input violates."""
    ctx = z3.Context()
    e, _ = _encode(f, ctx)
    out = []
    for v, what, bad in e.obl:
        s = z3.Solver(ctx=ctx)
        s.set(timeout=timeout_ms or TIMEOUT_MS[0])
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


def fits_type(f, vid, word_bits=64, timeout_ms=None):
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
    s.set(timeout=timeout_ms or TIMEOUT_MS[0])
    s.add(e.reach[v.block], ext(val.size() - tw, z3.Extract(tw - 1, 0, val)) != val)
    return s.check() == z3.unsat


def _norm(text):
    return re.sub(r"\((?:[-+]?\d+|\?)\) ", "", text)


def validate(passes, word_bits=64, arch=None):
    """Check a function's passes. passes = [(name, dump text), ...].

    Dumps from `lower` on are encoded with the machine semantics of arch
    (ppc64/ppc64le only); without it they are left out.
    """
    rep = {"checked": 0, "failures": [], "unsupported": None, "benign": 0}
    try:
        names = [n for n, _ in passes]
        cut = names.index("lower") if "lower" in names else len(names)
        if arch not in LOWERED_ARCHES:
            passes = passes[:cut]
        parsed = [(n, parse_dump(t)) for n, t in passes]
        for i, (_, f) in enumerate(parsed):
            if i >= cut:
                f.arch = arch
        prev_name, prev, prev_text = None, None, None
        seen_obl = set()
        for (name, f), (_, text) in zip(parsed, passes):
            for o in (ill_typed(f, word_bits) if getattr(f, "arch", None) is None else []):
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
                try:
                    cex = equivalent(prev, f)
                except SolverTimeout:  # e.g. magic-number division: count it, keep going
                    rep["timeouts"] = rep.get("timeouts", 0) + 1
                    cex = None
                else:
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


def dump_passes(go, pkgdir, funcs, goarch=None, extra_env=None, lowered=False, gcflags=""):
    """Generic-pass dumps, in pass order, up to (not including) lower.

    With lowered=True the dumps go on up to (not including) regalloc.

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
    r = subprocess.run([go, "build", f"-gcflags={gcflags} -d={flags}".strip(), "-o", os.devnull, "."],
                       cwd=pkgdir, env=env, capture_output=True, text=True)
    res = {}
    for fn in names:
        files = sorted(out.glob(f"{fn}_*__*.dump"), key=lambda p: int(p.name[len(fn) + 1:].split("__")[0]))
        if not files:
            raise RuntimeError(f"no SSA dump for {fn}: {r.stderr.strip()[:1500]}")
        passes = []
        for p in files:
            name = p.name.split("__", 1)[1][:-len(".dump")]
            if name == ("regalloc" if lowered else "lower"):
                break
            passes.append((name, p.read_text()))
        res[fn] = passes
    return res[funcs] if isinstance(funcs, str) else res


def check_source(go, src, funcs=None, goarch=None, lowered=False, gcflags=""):
    tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_"))
    try:
        (tmp / "main.go").write_text(src)
        (tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        names = funcs or re.findall(r"^func (v\d+)\(", src, re.M)
        try:
            dumps = dump_passes(go, tmp, names, goarch, lowered=lowered, gcflags=gcflags)
        except RuntimeError:  # one function broke the build: retry them one by one
            dumps = {}
            for fn in names:
                try:
                    dumps[fn] = dump_passes(go, tmp, fn, goarch, lowered=lowered, gcflags=gcflags)
                except RuntimeError as exc:
                    dumps[fn] = exc
        reps = {}
        for fn in names:
            if isinstance(dumps[fn], RuntimeError):
                reps[fn] = {"checked": 0, "failures": [], "unsupported": None, "build_error": str(dumps[fn])[:2000]}
            else:
                reps[fn] = validate(dumps[fn], 32 if goarch in ("386", "arm", "mips", "mipsle") else 64,
                                    goarch if lowered else None)
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
        p.add_argument("--timeout-ms", type=int, default=20000, help="per solver query")
        p.add_argument("--gcflags", default="", help='extra compiler flags, e.g. "-N -l"')
        p.add_argument("--lowered", action="store_true",
                       help="also check the lowered passes up to regalloc (amd64, ppc64, ppc64le)")
        if name == "check":
            p.add_argument("file")
            p.add_argument("--funcs")
        else:
            p.add_argument("--suite", default="core")
            p.add_argument("--seed", type=int, default=1)
            p.add_argument("--start", type=int, default=0)
            p.add_argument("--count", type=int, default=10)
    a = ap.parse_args(argv)
    TIMEOUT_MS[0] = a.timeout_ms
    if a.cmd == "check":
        reps = {a.file: check_source(a.go, Path(a.file).read_text(),
                                     a.funcs.split(",") if a.funcs else None, a.goarch, a.lowered, a.gcflags)}
    else:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import alt_compiler_diff as acd
        reps = {}
        for i in range(a.start, a.start + a.count):
            prog = acd.random_program(a.suite, a.seed, i)
            reps[f"{a.suite}-{a.seed}-{i:05d}"] = check_source(a.go, prog.source, goarch=a.goarch, lowered=a.lowered,
                                                               gcflags=a.gcflags)
    total = {"functions": 0, "unsupported": 0, "pairs": 0, "timeouts": 0, "failures": 0}
    for prog, fns in reps.items():
        for fn, r in fns.items():
            total["functions"] += 1
            total["unsupported"] += r["unsupported"] is not None
            if r.get("build_error"):
                total["build_errors"] = total.get("build_errors", 0) + 1
                print(json.dumps({"program": prog, "func": fn, "kind": "build_error",
                                  "error": r["build_error"].splitlines()[1:3]}))
            total["pairs"] += r["checked"]
            total["timeouts"] += r.get("timeouts", 0)
            for fl in r["failures"]:
                total["failures"] += 1
                print(json.dumps({"program": prog, "func": fn, **fl}, default=str))
    print(json.dumps(total), file=sys.stderr)
    return 1 if total["failures"] else 0


if __name__ == "__main__":
    sys.exit(main())
