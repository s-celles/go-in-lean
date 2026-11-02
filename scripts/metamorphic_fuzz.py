#!/usr/bin/env python3
"""Metamorphic differential fuzzing of the Go compiler on integer expressions.

For each random expression E(x, y; k1..kn) with constants k_i, three functions are emitted:
  c<i>(x, y)            E with the k_i written as constants (rewrite rules, constant folding)
  v<i>(x, y, k1..kn)    //go:noinline, constants passed at run time (the oracle)
  h<i>(x, y)            calls an inlinable helper with the constants as arguments
All three must agree on every input. Constants are biased to boundary values (0, ±1, MinInt,
MaxInt, width±1, powers of two ±1, and shift counts >= 2^63). Shift counts are unsigned.
Division/modulo use only non-zero constant divisors. Expressions whose constant parts do not
compile (constant overflow, vet-style errors) are dropped automatically.

Usage: metamorphic_fuzz.py SEED N OUTDIR   (writes OUTDIR/main.go; run it with any go)
"""
import os, random, re, subprocess, sys

TYPES = {"int8": (8, True), "int16": (16, True), "int32": (32, True), "int64": (64, True),
         "uint8": (8, False), "uint16": (16, False), "uint32": (32, False), "uint64": (64, False)}

def edge_consts(t):
    w, s = TYPES[t]
    lo, hi = (-(1 << (w - 1)), (1 << (w - 1)) - 1) if s else (0, (1 << w) - 1)
    c = {0, 1, 2, 3, w - 1, w, w + 1, hi, lo, hi - 1, lo + 1, 7, 0x55 & hi}
    for k in range(w):
        for d in (-1, 0, 1):
            v = (1 << k) + d
            if lo <= v <= hi: c.add(v)
            if s and lo <= -v <= hi: c.add(-v)
    return sorted(x for x in c if lo <= x <= hi)

SHIFT_COUNTS = [0, 1, 2, 7, 8, 15, 16, 31, 32, 33, 63, 64, 65, 127, 255, 256,
                1 << 31, 1 << 32, 1 << 62, 1 << 63, (1 << 63) + 1, (1 << 64) - 1, (1 << 64) - 2]

class Gen:
    def __init__(self, rnd):
        self.r = rnd; self.consts = []
    def const(self, t, val=None):
        if val is None: val = self.r.choice(edge_consts(t))
        self.consts.append((t, val))
        return ("k", len(self.consts) - 1, t)
    def count(self):
        if self.r.random() < 0.7:
            self.consts.append(("uint64", self.r.choice(SHIFT_COUNTS)))
            return ("k", len(self.consts) - 1, "uint64")
        return ("conv", "uint64", self.expr("uint" + self.r.choice(["8", "16", "64"]), 1))
    def expr(self, t, depth):
        r = self.r
        if depth <= 0 or r.random() < 0.25:
            return r.choice([("var", "x", t), ("var", "y", t), self.const(t)])
        k = r.random()
        if k < 0.30:
            op = r.choice(["+", "-", "*", "&", "|", "^", "&^"])
            a = self.expr(t, depth - 1)
            # rewrite rules mostly match "(op e (Const))": bias the right operand to a constant
            b = self.const(t) if r.random() < 0.5 else self.expr(t, depth - 1)
            if a[0] == "k" and b[0] == "k": a = ("var", "x", t)
            return ("bin", op, a, b, t)
        if k < 0.55:
            return ("shift", r.choice(["<<", ">>"]), self.expr(t, depth - 1), self.count(), t)
        if k < 0.65:
            d = self.const(t, r.choice([v for v in edge_consts(t) if v != 0]))
            return ("bin", r.choice(["/", "%"]), self.expr(t, depth - 1), d, t)
        if k < 0.75:
            return ("un", r.choice(["-", "^"]), self.expr(t, depth - 1), t)
        src = r.choice(list(TYPES))
        return ("conv", t, self.expr(src, depth - 1))

def render(e, mode):
    tag = e[0]
    if tag == "var": return e[1]
    if tag == "k":
        t = e[2]
        return f"{t}({mode['vals'][e[1]]})" if mode["const"] else f"k{e[1]}"
    if tag == "bin": return f"({render(e[2], mode)} {e[1]} {render(e[3], mode)})"
    if tag == "shift": return f"({render(e[2], mode)} {e[1]} {render(e[3], mode)})"
    if tag == "un": return f"({e[1]}{render(e[2], mode)})"
    if tag == "conv": return f"{e[1]}({render(e[2], mode)})"
    raise ValueError(tag)

CANARY = "--canary" in sys.argv

def canary(g):
    """((x >> 2^63) & 3) << 1 on int64: golang/go#82763 (wrong on go1.25..1.27, master babb75be)."""
    t = "int64"
    sh = ("shift", ">>", ("var", "x", t), g.const("uint64", 1 << 63), t)
    return t, ("shift", "<<", ("bin", "&", sh, g.const(t, 3), t), g.const("uint64", 1), t)

BRANCHY = "--branchy" in sys.argv

def program(seed, n):
    rnd = random.Random(seed)
    funcs, checks = [], []
    for i in range(n):
        g = Gen(rnd)
        t = rnd.choice(list(TYPES))
        e = g.expr(t, rnd.randint(2, 4))
        branch = None
        if BRANCHY and rnd.random() < 0.6:
            # r := e; if (e3 cmp K) { r = e2 }: branch facts feed the prove pass
            e2 = g.expr(t, rnd.randint(1, 3))
            ct = rnd.choice(list(TYPES))
            e3 = g.expr(ct, rnd.randint(0, 2))
            branch = (rnd.choice(["<", "<=", ">", ">=", "==", "!="]), e3, g.const(ct), e2)
        if CANARY and i == 0:
            t, e = canary(g); branch = None
        vals = [v for _, v in g.consts]
        params = ", ".join(f"k{j} {ct}" for j, (ct, _) in enumerate(g.consts))
        def body(mode):
            r = render(e, mode)
            if branch is None:
                return r
            op, e3, k, e2 = branch
            return f"func() {t} {{ r := {r}; if {render(e3, mode)} {op} {render(k, mode)} {{ r = {render(e2, mode)} }}; return r }}()"
        cexpr = body({"const": True, "vals": vals})
        vexpr = body({"const": False, "vals": vals})
        sep = ", " if params else ""
        args = ", ".join(f"{ct}({v})" for ct, v in g.consts)
        funcs.append(f"//go:noinline\nfunc c{i}(x, y {t}) {t} {{ return {cexpr} }}\n"
                     f"//go:noinline\nfunc v{i}(x, y {t}{sep}{params}) {t} {{ return {vexpr} }}\n"
                     f"func hh{i}(x, y {t}{sep}{params}) {t} {{ return {vexpr} }}\n"
                     f"//go:noinline\nfunc h{i}(x, y {t}) {t} {{ return hh{i}(x, y{sep}{args}) }}\n")
        checks.append(f"\tfor _, p := range pairs {{\n\t\tx, y := {t}(p[0]), {t}(p[1])\n"
                      f"\t\tvv := v{i}(x, y{sep}{args})\n"
                      f"\t\tif cc := c{i}(x, y); cc != vv {{ report({i}, \"const\", uint64(x), uint64(y), uint64(cc), uint64(vv)) }}\n"
                      f"\t\tif hv := h{i}(x, y); hv != vv {{ report({i}, \"inline\", uint64(x), uint64(y), uint64(hv), uint64(vv)) }}\n\t}}\n")
    return funcs, checks

HEADER = '''// Code generated by scripts/metamorphic_fuzz.py. DO NOT EDIT.
package main

import (
	"fmt"
	"os"
)

var pairs = [][2]uint64{{0, 0}, {1, 2}, {^uint64(0), 1}, {1 << 63, 3}, {0x7f, 0x80}, {0x8000, 0xffff},
	{0x80000000, 0x7fffffff}, {0x0123456789abcdef, 0xfedcba9876543210}, {5, ^uint64(0)}, {0xff, 0x100}}

var bad = 0

func report(i int, kind string, x, y, got, want uint64) {
	bad++
	if bad <= 50 {
		fmt.Printf("expr %d (%s): x=%#x y=%#x got %#x want %#x\\n", i, kind, x, y, got, want)
	}
}
'''

def write(seed, n, outdir, drop=set()):
    funcs, checks = program(seed, n)
    keep = [i for i in range(n) if i not in drop]
    src = HEADER + "\n".join(funcs[i] for i in keep)
    src += "\nfunc main() {\n" + "".join(checks[i] for i in keep)
    src += '\tfmt.Printf("seed %d: %d expressions, %d mismatches\\n", ' + f"{seed}, {len(keep)}" + ', bad)\n\tif bad > 0 {\n\t\tos.Exit(1)\n\t}\n}\n'
    open(os.path.join(outdir, "main.go"), "w").write(src)
    return src

def main():
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    seed, n, outdir = int(argv[0]), int(argv[1]), argv[2]
    gobin = os.environ.get("GO", "go")
    os.makedirs(outdir, exist_ok=True)
    if not os.path.exists(os.path.join(outdir, "go.mod")):
        open(os.path.join(outdir, "go.mod"), "w").write("module fuzz\ngo 1.25\n")
    drop = set()
    for _ in range(30):
        src = write(seed, n, outdir, drop)
        r = subprocess.run([gobin, "vet", "."], cwd=outdir, capture_output=True, text=True)
        r = subprocess.run([gobin, "build", "-o", os.devnull, "."], cwd=outdir, capture_output=True, text=True)
        if r.returncode == 0: break
        lines = src.splitlines()
        newly = set()
        for m in re.finditer(r"main\.go:(\d+):", r.stderr):
            ln = int(m.group(1))
            for j in range(ln - 1, -1, -1):
                mm = re.match(r"func [cvh]h?(\d+)\(", lines[j])
                if mm: newly.add(int(mm.group(1))); break
                mm = re.search(r"\b[vch](\d+)\(x, y", lines[j])
                if mm and lines[j].startswith("\t"): newly.add(int(mm.group(1))); break
        if not newly: raise SystemExit("cannot fix compile errors:\n" + r.stderr[:2000])
        drop |= newly
    print(f"seed {seed}: wrote {n - len(drop)} expressions ({len(drop)} dropped for compile errors)")

if __name__ == "__main__":
    main()
