#!/usr/bin/env python3
"""SMT-guided input selection for alt_compiler_diff.py (needs the z3 module).

A generated function is a small loop-free integer expression of x and y, so
z3 can find inputs that land exactly on its semantic boundaries: shift
counts at w-1/w/0, signed division overflow (MinInt / -1), divisors of +-1,
comparison operands that are equal or adjacent, both arms of every select,
narrowing conversions that drop set bits, wrapping arithmetic, zero and
top-bit arguments of math/bits. Each boundary is conjoined with the path
condition of the selects above it, so the subexpression is actually used.

The encoding follows the Go specification, but it is only used to choose
inputs: the verdict still comes from the Lean oracle, so an encoding mistake
costs coverage, never a false report.
"""

import random

import z3

M64 = (1 << 64) - 1
_CTX = [None]  # current z3 context (a fresh one per query, for determinism)


def _val(v, w):
    return z3.BitVecVal(v, w, _CTX[0])


CMP = {"lt", "le", "gt", "ge", "eq", "ne"}


def node_type(n):
    """Go type (width, signed) of a node; None for a comparison (bool)."""
    k = n["k"]
    if k == "bin" and n["op"] in CMP:
        return None
    if k in ("lit", "var", "conv", "sel"):
        return n["t"]
    if k in ("un", "bin"):
        return node_type(n["a"])
    if k == "bits":
        return (64, True) if n["op"] in ("oc", "lz", "tz", "len") else (n["w"], False)
    if k == "rot":
        return (n["w"], False)
    raise ValueError(f"node kind {k!r} is not supported by the SMT encoding")


def _ext(v, w_from, w_to, signed):
    if w_to == w_from:
        return v
    if w_to < w_from:
        return z3.Extract(w_to - 1, 0, v)
    return (z3.SignExt if signed else z3.ZeroExt)(w_to - w_from, v)


def _popcount(v, w):
    return sum((z3.ZeroExt(63, z3.Extract(i, i, v)) for i in range(w)), _val(0, 64))


def _lz(v, w):
    r = _val(w, 64)
    for i in range(w):  # the highest set bit wins: build from the bottom up
        r = z3.If(z3.Extract(i, i, v) == 1, _val(w - 1 - i, 64), r)
    return r


def _tz(v, w):
    r = _val(w, 64)
    for i in reversed(range(w)):  # the lowest set bit wins
        r = z3.If(z3.Extract(i, i, v) == 1, _val(i, 64), r)
    return r


def _rev(v, w):
    return z3.Concat(*[z3.Extract(i, i, v) for i in range(w)]) if w > 1 else v


def _rb(v, w):
    return z3.Concat(*[z3.Extract(8 * i + 7, 8 * i, v) for i in range(w // 8)])


class Encoder:
    """Encodes IR trees over the 64-bit inputs X and Y and collects targets."""

    def __init__(self, X, Y):
        self.X, self.Y = X, Y
        self.targets = []  # (label, z3 Bool)

    def target(self, label, cond, path):
        self.targets.append((label, z3.And(*path, cond) if path else cond))

    def enc(self, n, path=()):
        k = n["k"]
        if k == "lit":
            w, _ = n["t"]
            return _val(n["v"] % (1 << w), w)
        if k == "var":
            w, _ = n["t"]
            return _ext(self.X if n["which"] == "x" else self.Y, 64, w, False)
        if k == "un":
            a = self.enc(n["a"], path)
            w, s = node_type(n)
            if n["op"] == "neg":
                if s:
                    self.target("neg-min", a == _val(1 << (w - 1), w), path)
                return -a
            return ~a
        if k == "conv":
            w, s = n["t"]
            src = n["a"]
            a = self.enc(src, path)
            st = node_type(src)
            if st is None:
                return z3.If(a, _val(1, w), _val(0, w))
            ws, ss = st
            if w < ws:
                lo = z3.Extract(w - 1, 0, a)
                self.target("trunc-topbit", z3.And(z3.Extract(w - 1, w - 1, a) == 1,
                                                   z3.Extract(ws - 1, w, a) != 0), path)
                self.target("trunc-fits", z3.And(z3.Extract(ws - 1, w, a) == 0, lo != 0), path)
            elif w > ws and ss:
                self.target("sext-neg", z3.Extract(ws - 1, ws - 1, a) == 1, path)
            return _ext(a, ws, w, ss)
        if k == "sel":
            c = self.enc(n["c"], path)
            self.target("sel-true", c, path)
            self.target("sel-false", z3.Not(c), path)
            a = self.enc(n["a"], path + (c,))
            b = self.enc(n["b"], path + (z3.Not(c),))
            return z3.If(c, a, b)
        if k == "bits":
            w = n["w"]
            a = self.enc(n["a"], path)
            op = n["op"]
            self.target("bits-zero", a == 0, path)
            self.target("bits-top", z3.Extract(w - 1, w - 1, a) == 1, path)
            if op == "oc":
                return _popcount(a, w)
            if op == "lz":
                return _lz(a, w)
            if op == "tz":
                return _tz(a, w)
            if op == "len":
                return _val(w, 64) - _lz(a, w)
            if op == "rev":
                return _rev(a, w)
            if op == "rb":
                return _rb(a, w)
            raise ValueError(op)
        if k == "rot":
            w = n["w"]
            a = self.enc(n["a"], path)
            kk = n["c"]["v"] % (1 << 64)
            if kk >= 1 << 63:
                kk -= 1 << 64
            self.target("rot-top", z3.Extract(w - 1, w - 1, a) == 1, path)
            return z3.RotateLeft(a, kk % w)
        if k == "bin":
            return self.binary(n, path)
        raise ValueError(f"node kind {k!r} is not supported by the SMT encoding")

    def binary(self, n, path):
        op = n["op"]
        a = self.enc(n["a"], path)
        if op in ("shl", "shr"):
            w, s = node_type(n["a"])
            ct = node_type(n["b"])
            c = self.enc(n["b"], path)
            cw, cs = ct
            c64 = _ext(c, cw, 64, False)
            if cs:
                self.target("count-negative", z3.Extract(cw - 1, cw - 1, c) == 1, path)
            for v, label in ((w - 1, "count-w-1"), (w, "count-w"), (0, "count-0")):
                if v < (1 << cw):
                    self.target(label, c64 == v, path)
            if op == "shr" and s:
                self.target("sra-neg", z3.And(z3.Extract(w - 1, w - 1, a) == 1,
                                              z3.ULT(c64, w)), path)
            big = z3.UGE(c64, w)
            cw_ = _ext(c64, 64, w, False)
            if op == "shl":
                return z3.If(big, _val(0, w), a << cw_)
            if s:
                return z3.If(big, a >> (w - 1), a >> cw_)
            return z3.If(big, _val(0, w), z3.LShR(a, cw_))
        b = self.enc(n["b"], path)
        t = node_type(n["a"])
        w, s = t
        if op in CMP:
            self.target("cmp-eq", a == b, path)
            self.target("cmp-adj", a == b + 1, path)
            self.target("cmp-adj", a + 1 == b, path)
            if s:
                lt, le, gt, ge = a < b, a <= b, a > b, a >= b
            else:
                lt, le, gt, ge = z3.ULT(a, b), z3.ULE(a, b), z3.UGT(a, b), z3.UGE(a, b)
            return {"lt": lt, "le": le, "gt": gt, "ge": ge, "eq": a == b, "ne": a != b}[op]
        if op in ("div", "mod"):
            if n.get("panic_site"):
                self.target("div-zero", b == 0, path)
            self.target("div-one", b == 1, path)
            if s:
                minv = _val(1 << (w - 1), w)
                self.target("div-overflow", z3.And(a == minv, b == _val(-1, w)), path)
                self.target("div-neg", z3.And(z3.Extract(w - 1, w - 1, a) == 1, b != 0), path)
            else:
                self.target("div-big", z3.And(z3.Extract(w - 1, w - 1, b) == 1), path)
            if op == "div":
                return (a / b) if s else z3.UDiv(a, b)
            return z3.SRem(a, b) if s else z3.URem(a, b)
        if op == "add":
            r = a + b
            self.target("add-wrap", z3.ULT(r, a), path)
            return r
        if op == "sub":
            self.target("sub-wrap", z3.ULT(a, b), path)
            return a - b
        if op == "mul":
            self.target("mul-wrap", z3.Not(z3.BVMulNoOverflow(a, b, s)), path)
            return a * b
        if op == "and":
            return a & b
        if op == "or":
            return a | b
        if op == "xor":
            return a ^ b
        if op == "andnot":
            return a & ~b
        if op == "min":
            return z3.If((a < b) if s else z3.ULT(a, b), a, b)
        if op == "max":
            return z3.If((a > b) if s else z3.UGT(a, b), a, b)
        raise ValueError(op)


def evaluate(n, x, y):
    """Value of a tree at (x, y) as an unsigned integer of its width (0/1 for bool)."""
    _CTX[0] = z3.Context()
    X, Y = _val(x & M64, 64), _val(y & M64, 64)
    v = z3.simplify(Encoder(X, Y).enc(n))
    if z3.is_bool(v):
        return 1 if z3.is_true(v) else 0
    return v.as_long()


def as_uint64(n, v):
    """The uint64 the generated Go function returns for value v of tree n."""
    t = node_type(n)
    if t is None:
        return v
    w, s = t
    if s and v >= 1 << (w - 1):
        v -= 1 << w
    return v & M64


def smt_pairs(tree, n, rng, timeout_ms=400):
    """Up to n distinct (x, y) pairs hitting boundaries of tree, and their labels.

    Deterministic for a given rng state and z3 version."""
    # z3 hash-conses terms per context: reusing one context makes the models
    # depend on earlier queries, so every call gets a fresh one
    ctx = _CTX[0] = z3.Context()
    X, Y = z3.BitVec("x", 64, ctx), z3.BitVec("y", 64, ctx)
    e = Encoder(X, Y)
    root = e.enc(tree)
    targets = list(e.targets)
    rng.shuffle(targets)
    if not z3.is_bool(root):
        # whole-result boundaries come last: the structural ones are rarer
        w = root.size()
        tail = [("result-zero", root == 0), ("result-ones", root == _val(-1, w)),
                ("result-topbit", z3.Extract(w - 1, w - 1, root) == 1)]
        rng.shuffle(tail)
        targets += tail
    pairs, labels = [], []
    seen = set()
    for label, cond in targets:
        if len(pairs) >= n:
            break
        s = z3.Solver(ctx=ctx)
        s.set("timeout", timeout_ms)
        s.set("random_seed", rng.randrange(1 << 30))
        s.add(cond)
        # prefer an input not already chosen, and not the trivial (0, 0)
        for p in seen:
            s.add(z3.Or(X != p[0], Y != p[1]))
        if s.check() != z3.sat:
            continue
        m = s.model()
        p = (m.eval(X, model_completion=True).as_long(),
             m.eval(Y, model_completion=True).as_long())
        seen.add(p)
        pairs.append(p)
        labels.append(label)
    return pairs, labels


def fill(pairs, n, pool, rng):
    """Complete pairs to n entries with distinct random pool pairs."""
    out = list(pairs)
    tries = 0
    while len(out) < n and tries < 100 * n:
        p = (rng.choice(pool), rng.choice(pool))
        tries += 1
        if p not in out:
            out.append(p)
    return out


if __name__ == "__main__":
    t = {"k": "bin", "op": "shr", "a": {"k": "var", "t": (16, True), "which": "x"},
         "b": {"k": "var", "t": (64, False), "which": "y"}}
    print(smt_pairs(t, 6, random.Random(0)))
