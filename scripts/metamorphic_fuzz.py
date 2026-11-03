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
        self.r = rnd; self.consts = []; self.count_var = None
    def const(self, t, val=None):
        if val is None: val = self.r.choice(edge_consts(t))
        self.consts.append((t, val))
        return ("k", len(self.consts) - 1, t)
    def count(self):
        if COUNTVAR and self.count_var is not None and self.r.random() < 0.5:
            # the count is the run-time variable itself: the compiled c/h versions keep an
            # unbounded count, so the lowering emits the width mask (CMP const [w] count)
            name, vt = self.count_var
            return ("conv", "uint64", ("var", name, vt))
        if self.r.random() < 0.7:
            self.consts.append(("uint64", self.r.choice(SHIFT_COUNTS)))
            return ("k", len(self.consts) - 1, "uint64")
        return ("conv", "uint64", self.expr("uint" + self.r.choice(["8", "16", "64"]), 1))
    def expr(self, t, depth):
        r = self.r
        if depth <= 0 or r.random() < 0.25:
            return r.choice([("var", "x", t), ("var", "y", t), self.const(t)])
        if (BITS or CARRY) and r.random() < 0.25:
            return self.call(t, depth)
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

    def call(self, t, depth):
        """math/bits intrinsics and the min/max builtins (arch-specific lowering rules)."""
        r = self.r
        if CARRY and r.random() < 0.35:
            # Add64/Sub64 (carry/borrow tuple): the lowering emits flag-writing ALU ops
            # (ADDQcarry, ADDLcarry chains, SUBS/RSBS shifts, ANDCC) that share the
            # flags register with neighbouring comparisons - the golang/go#82825 class.
            fn = r.choice(["Add64", "Sub64"])
            which = r.choice([0, 1])
            a = self.expr("uint64", depth - 1)
            b = self.expr("uint64", depth - 1)
            c = ("conv", "uint64", self.expr("uint8", 0))
            return ("carry", fn, which, a, b, c, t)
        if r.random() < 0.3:
            return ("mm", r.choice(["min", "max"]), self.expr(t, depth - 1), self.expr(t, depth - 1), t)
        w = TYPES[t][0]
        u = f"uint{w}"
        fns = ["OnesCount", "LeadingZeros", "TrailingZeros", "Len", "Reverse", "RotateLeft"]
        if w > 8: fns.append("ReverseBytes")
        fn = r.choice(fns)
        arg = self.expr(u, depth - 1)
        extra = None
        if fn == "RotateLeft":
            extra = ("conv", "int", self.expr("int8", 1)) if r.random() < 0.5 else \
                    ("lit", r.choice([-65, -1, 0, 1, 3, w - 1, w, w + 1, 63, 64]))
        return ("call", f"{fn}{w}", arg, extra, t)

def render(e, mode):
    tag = e[0]
    # x, y are declared with the function's type; a var node of another type is a conversion
    if tag == "var": return f"{e[2]}({e[1]})"
    if tag == "k":
        t = e[2]
        if not mode["const"]:
            return f"k{e[1]}"
        if LATE:
            return late_const(t, mode["vals"][e[1]])
        return f"{t}({mode['vals'][e[1]]})"
    if tag == "bin": return f"({render(e[2], mode)} {e[1]} {render(e[3], mode)})"
    if tag == "shift": return f"({render(e[2], mode)} {e[1]} {render(e[3], mode)})"
    if tag == "un": return f"({e[1]}{render(e[2], mode)})"
    if tag == "conv": return f"{e[1]}({render(e[2], mode)})"
    if tag == "lit": return str(e[1])
    if tag == "mm": return f"{e[1]}({render(e[2], mode)}, {render(e[3], mode)})"
    if tag == "call":
        args = render(e[2], mode) + (", " + render(e[3], mode) if e[3] is not None else "")
        return f"{e[4]}(bits.{e[1]}({args}))"
    if tag == "carry":
        _, fn, which, a, b, c, t = e
        hi, lo = ("carry", "sum") if fn == "Add64" else ("borrow", "diff")
        if which == 0:
            hi, sel = "_", lo
        else:
            lo, sel = "_", hi
        return (f"{t}(func() uint64 {{ {hi}, {lo} := bits.{fn}({render(a, mode)}, "
                f"{render(b, mode)}, {render(c, mode)}); return {sel} }}())")
    raise ValueError(tag)

CANARY = "--canary" in sys.argv

def canary(g):
    """((x >> 2^63) & 3) << 1 on int64: golang/go#82763 (wrong on go1.25..1.27, master babb75be)."""
    t = "int64"
    sh = ("shift", ">>", ("var", "x", t), g.const("uint64", 1 << 63), t)
    return t, ("shift", "<<", ("bin", "&", sh, g.const(t, 3), t), g.const("uint64", 1), t)

BRANCHY = "--branchy" in sys.argv
BITS = "--bits" in sys.argv     # math/bits intrinsics and min/max builtins
INDEX = "--index" in sys.argv   # use the expression as an array index (bounds-check elimination)
LATE = "--late" in sys.argv     # constants become loads from read-only data, folded only in lower
COUNTVAR = "--countvar" in sys.argv  # some shift counts become the variable x/y, and branches
                                     # sometimes compare that same value with a width-class
                                     # constant (the flag-sharing shape of golang/go#82825)
CARRY = "--carry" in sys.argv        # bits.Add64/Sub64 tuples: flag-writing carry chains
                                     # (ADDQcarry, ADDLcarry, SUBS/RSBS shifts, ANDCC) sharing
                                     # the flags register with neighbouring comparisons


def late_const(t, v):
    """A constant the generic optimiser cannot fold: bytes loaded from the read-only string lateS
    (lateS[i] == i), recombined with shifts and ORs. Arch lowering folds the loads (symIsRO), so the
    arch-specific constant-folding rules see the value instead of the generic ones."""
    w = TYPES[t][0]
    u = v % (1 << w)
    parts = []
    for i in range(w // 8):
        b = (u >> (8 * i)) & 0xFF
        if b:
            parts.append(f"uint{w}(lateS[{b}])" + (f"<<{8 * i}" if i else ""))
    if not parts:
        parts = [f"uint{w}(lateS[0])"]
    return f"{t}(" + " | ".join(parts) + ")"
TABLES = [1, 7, 8, 16, 255, 256]

def program(seed, n):
    rnd = random.Random(seed)
    funcs, checks = [], []
    for i in range(n):
        g = Gen(rnd)
        t = rnd.choice(list(TYPES))
        if COUNTVAR:
            g.count_var = (rnd.choice(["x", "y"]), t)
        e = g.expr(t, rnd.randint(2, 4))
        branch = None
        if COUNTVAR and rnd.random() < 0.4 and g.count_var is not None:
            # compare the count variable against a width-class constant (63/64/65/127/128
            # are in the uint64 edge pool): with ==/!= this shares the shift mask's CMP.
            # The condition feeds an all-constant phi (b := 0; if cond { b = 1 }), which
            # phiopt materialises as a SETcc value - the second flag consumer of
            # golang/go#82825.
            name, vt = g.count_var
            branch = ("countcmp", rnd.choice(["<", "<=", "==", "!=", ">", ">="]),
                      ("conv", "uint64", ("var", name, vt)), g.const("uint64"))
        if BRANCHY and branch is None and rnd.random() < 0.6:
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
            if branch[0] == "countcmp":
                _, op, e3, k = branch
                return (f"func() {t} {{ r := {r}; b := 0; "
                        f"if {render(e3, mode)} {op} {render(k, mode)} {{ b = 1 }}; "
                        f"return r + {t}(b) }}()")
            op, e3, k, e2 = branch
            return f"func() {t} {{ r := {r}; if {render(e3, mode)} {op} {render(k, mode)} {{ r = {render(e2, mode)} }}; return r }}()"
        cexpr = body({"const": True, "vals": vals})
        vexpr = body({"const": False, "vals": vals})
        if INDEX:
            # index tab<N>[int(e)] (optionally masked or guarded); a panic is reported as a sentinel
            n = rnd.choice(TABLES)
            form = rnd.choice(["plain", "mask", "guard", "mod"])
            def idx(ex):
                i = f"int({ex})"
                if form == "mask" and n & (n - 1) == 0: i = f"int(uint({ex}) & {n - 1})"
                if form == "mod": i = f"int(uint({ex}) % {n})"
                return i
            def wrap(ex):
                i = idx(ex)
                if form == "guard":
                    return (f"func() (r {t}) {{ defer func() {{ if recover() != nil {{ r = {t}(0x5A) }} }}(); "
                            f"if i := {i}; i >= 0 && i < len(tab{n}) {{ return {t}(tab{n}[i]) }}; return {t}(0x33) }}()")
                return (f"func() (r {t}) {{ defer func() {{ if recover() != nil {{ r = {t}(0x5A) }} }}(); "
                        f"return {t}(tab{n}[{i}]) }}()")
            cexpr, vexpr = wrap(cexpr), wrap(vexpr)
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
	"math/bits"
	"os"
)

var _ = bits.Len

var pairs = [][2]uint64{{0, 0}, {1, 2}, {^uint64(0), 1}, {1 << 63, 3}, {0x7f, 0x80}, {0x8000, 0xffff},
	{0x80000000, 0x7fffffff}, {0x0123456789abcdef, 0xfedcba9876543210}, {5, ^uint64(0)}, {0xff, 0x100}}

var bad = 0

const lateS = "\\x00\\x01\\x02\\x03\\x04\\x05\\x06\\x07\\x08\\x09\\x0a\\x0b\\x0c\\x0d\\x0e\\x0f\\x10\\x11\\x12\\x13\\x14\\x15\\x16\\x17\\x18\\x19\\x1a\\x1b\\x1c\\x1d\\x1e\\x1f\\x20\\x21\\x22\\x23\\x24\\x25\\x26\\x27\\x28\\x29\\x2a\\x2b\\x2c\\x2d\\x2e\\x2f\\x30\\x31\\x32\\x33\\x34\\x35\\x36\\x37\\x38\\x39\\x3a\\x3b\\x3c\\x3d\\x3e\\x3f\\x40\\x41\\x42\\x43\\x44\\x45\\x46\\x47\\x48\\x49\\x4a\\x4b\\x4c\\x4d\\x4e\\x4f\\x50\\x51\\x52\\x53\\x54\\x55\\x56\\x57\\x58\\x59\\x5a\\x5b\\x5c\\x5d\\x5e\\x5f\\x60\\x61\\x62\\x63\\x64\\x65\\x66\\x67\\x68\\x69\\x6a\\x6b\\x6c\\x6d\\x6e\\x6f\\x70\\x71\\x72\\x73\\x74\\x75\\x76\\x77\\x78\\x79\\x7a\\x7b\\x7c\\x7d\\x7e\\x7f\\x80\\x81\\x82\\x83\\x84\\x85\\x86\\x87\\x88\\x89\\x8a\\x8b\\x8c\\x8d\\x8e\\x8f\\x90\\x91\\x92\\x93\\x94\\x95\\x96\\x97\\x98\\x99\\x9a\\x9b\\x9c\\x9d\\x9e\\x9f\\xa0\\xa1\\xa2\\xa3\\xa4\\xa5\\xa6\\xa7\\xa8\\xa9\\xaa\\xab\\xac\\xad\\xae\\xaf\\xb0\\xb1\\xb2\\xb3\\xb4\\xb5\\xb6\\xb7\\xb8\\xb9\\xba\\xbb\\xbc\\xbd\\xbe\\xbf\\xc0\\xc1\\xc2\\xc3\\xc4\\xc5\\xc6\\xc7\\xc8\\xc9\\xca\\xcb\\xcc\\xcd\\xce\\xcf\\xd0\\xd1\\xd2\\xd3\\xd4\\xd5\\xd6\\xd7\\xd8\\xd9\\xda\\xdb\\xdc\\xdd\\xde\\xdf\\xe0\\xe1\\xe2\\xe3\\xe4\\xe5\\xe6\\xe7\\xe8\\xe9\\xea\\xeb\\xec\\xed\\xee\\xef\\xf0\\xf1\\xf2\\xf3\\xf4\\xf5\\xf6\\xf7\\xf8\\xf9\\xfa\\xfb\\xfc\\xfd\\xfe\\xff"

var _ = lateS

var (
	tab1   [1]int8
	tab7   [7]int8
	tab8   [8]int8
	tab16  [16]int8
	tab255 [255]int8
	tab256 [256]int8
)

func init() {
	fill := func(s []int8) {
		for i := range s {
			s[i] = int8(i*7 + 1)
		}
	}
	fill(tab1[:]); fill(tab7[:]); fill(tab8[:]); fill(tab16[:]); fill(tab255[:]); fill(tab256[:])
}

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
    # Validate for the target GOARCH (inherited from the environment); -gcflags=-e reports every
    # error, not just the first ten, so each round drops all failing expressions.
    for _ in range(30):
        src = write(seed, n, outdir, drop)
        r = subprocess.run([gobin, "build", "-gcflags=-e", "-o", os.devnull, "."], cwd=outdir, capture_output=True, text=True)
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
    else:
        raise SystemExit("compile errors remain after 30 rounds:\n" + r.stderr[:2000])
    print(f"seed {seed}: wrote {n - len(drop)} expressions ({len(drop)} dropped for compile errors)")

if __name__ == "__main__":
    main()
