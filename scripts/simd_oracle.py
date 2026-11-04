#!/usr/bin/env python3
"""Lean-oracle differential fuzzer for GOEXPERIMENT=simd integer chains (J3).

Builds random typed SIMD chains over the integer and mask types of the simd
package (arithmetic, logic, and-not, min/max, shifts and rotates by constant
counts, comparisons producing masks, mask algebra, IfElse, Masked, ToMask /
ToInt) and emits, from the same IR:

* `exprs.json`  - the chains in RPN form for `lake exe oracle-simd` (the
  Lean model of the package semantics, evaluated at the 128-bit size);
* `gomain/main.go` - the same chains as simd package code, printing the same
  `expr <i>: 0x<hex>` FNV-1a checksum of the first min(4, 128/w) lanes.

The campaign runs the Go program with GODEBUG=simd=128 (every configuration
can run 128-bit vectors, hardware or emulated), so the Lean oracle compares
the *specification* against the toolchain. The cross-configuration oracle of
scripts/simd_fuzz.py stays the other half: it sees divergences between
implementations; this one sees classes where every implementation is wrong
together (docs/fuzzing-vision.md, milestone J3).

Usage: simd_oracle.py SEED N OUTDIR
Environment: GO (toolchain under test, default "go"), ORACLE_SIMD (default
  the lake exe), GODEBUG_S (default "simd=128").
"""
import json, os, random, subprocess, sys

# (width, signed) for the integer vector types; masks follow the width
VT = [(w, s) for w in (8, 16, 32, 64) for s in (False, True)]
GONAME = {(w, sg): f"{'Uint' if not sg else 'Int'}{w}s" for w in (8, 16, 32, 64) for sg in (False, True)}

def load_avail():
    """Method availability per vector type, parsed from simd_stubs.go so the
    generator follows the tree (the method sets are heterogeneous: Uint8s
    lacks GreaterEqual, Int64s lacks Max, ...)."""
    import re, subprocess
    goroot = os.environ.get("GOROOT")
    if not goroot:
        goroot = subprocess.run([os.environ.get("GO", "go"), "env", "GOROOT"],
                                capture_output=True, text=True).stdout.strip()
    path = os.path.join(goroot, "src", "simd", "simd_stubs.go")
    meth = re.compile(r"^func \(x (\w+)\) (\w+)\(")
    avail = {}
    for line in open(path):
        m = meth.match(line)
        if m:
            avail.setdefault(m.group(1), set()).add(m.group(2))
    return avail

AVAIL = {}  # filled in main/run: GONAME -> set of method names
ELEM = {(w, sg): f"{'u' if not sg else ''}int{w}" for w in (8, 16, 32, 64) for sg in (False, True)}

# the fixed input tables (mirrored in both emissions), >= 16 lanes each
I64 = [0, 1, -1, 2, -2, 3, -3, 7, -7, 120, -120, 85, -85, 170, -170,
       1 << 30, -(1 << 30), 0x55, 0xAA, -1 << 12, 4095]


def table(w, s):
    if s:
        vals = [((v + (1 << (w - 1))) % (1 << w)) - (1 << (w - 1)) for v in I64]
    else:
        vals = [v % (1 << w) for v in I64]
    return vals[:max(16, 128 // w)]


def lane_pool(w, s, r):
    if s:
        lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
        return r.choice([0, 1, -1, 2, -2, lo, hi, hi - 1, lo + 1, hi // 2, 85, -(1 << (w - 2))])
    hi = (1 << w) - 1
    return r.choice([0, 1, 2, 3, 7, hi, hi - 1, hi // 2 + 1, 1 << (w - 1), 85, 170])


class Gen:
    """Typed chain IR; the pool carries (node, kind) where kind is
    ("vec", (w, s)) or ("mask", w)."""

    def __init__(self, r):
        self.r = r
        self.tables = {t: table(*t) for t in VT}

    def leaf(self, t):
        r = self.r
        if r.random() < 0.5:
            # Load from the fixed table - the RPN carries the same lanes
            return {"k": "load", "t": t}
        v = lane_pool(t[0], t[1], r)
        return {"k": "bcast", "t": t, "v": v}

    def build_vec(self, t, d):
        r = self.r
        if d <= 0 or r.random() < 0.35:
            return self.leaf(t)
        w, s = t
        x = r.random()
        av = AVAIL.get(GONAME[t], set())
        x = r.random()
        if x < 0.40:
            ops = [o for o in ("Add", "Sub", "Mul", "And", "Or", "Xor", "AndNot", "Min", "Max") if o in av]
            if ops:
                op = r.choice(ops)
                return {"k": "bin", "op": op, "t": t,
                        "a": self.build_vec(t, d - 1), "b": self.build_vec(t, d - 1)}
        if x < 0.55:
            ops = [o for o in ("ShiftAllLeft", "ShiftAllRight") if o in av]
            if ops:
                op = r.choice(ops)
                c = r.choice([0, 1, 2, 3, 7, 8, w - 1, w, w + 1, 2 * w + 1])
                return {"k": "shift", "op": op, "t": t, "c": c, "a": self.build_vec(t, d - 1)}
        if x < 0.62 and "RotateAllLeft" in av:
            c = r.choice([0, 1, 2, 3, 7, w - 1, w, w + 1, 2 * w + 1, 2 ** 32])
            return {"k": "rot", "t": t, "c": c, "a": self.build_vec(t, d - 1)}
        if x < 0.78 and "IfElse" in av:
            m = self.build_cmp(t, d)
            return {"k": "sel", "t": t, "m": m,
                    "a": self.build_vec(t, d - 1), "b": self.build_vec(t, d - 1)}
        if x < 0.88 and "Masked" in av:
            m = self.build_cmp(t, d)
            return {"k": "masked", "t": t, "m": m, "a": self.build_vec(t, d - 1)}
        return self.build_vec(t, d)

    def build_cmp(self, t, d):
        """A mask-producing node of width t[0]: a comparison, or mask algebra."""
        r = self.r
        w = t[0]
        av = AVAIL.get(GONAME[t], set())
        if d <= 0 or r.random() < 0.6:
            ops = [o for o in ("Equal", "NotEqual", "Less", "LessEqual", "Greater", "GreaterEqual") if o in av]
            op = r.choice(ops or ["Equal"])
            return {"k": "cmp", "op": op, "w": w, "s": t[1],
                    "a": self.build_vec(t, d - 1), "b": self.build_vec(t, d - 1)}
        x = r.random()
        if x < 0.5:
            op = r.choice(["And", "Or", "Xor", "Equal"])
            return {"k": "mbin", "op": op, "w": w,
                    "a": self.build_cmp(t, d - 1), "b": self.build_cmp(t, d - 1)}
        if x < 0.75:
            return {"k": "mun", "w": w, "a": self.build_cmp(t, d - 1)}
        # a mask from ToMask on a signed vector of the same width
        return {"k": "tomask", "w": w, "a": self.build_vec((w, True), d - 1)}

    def build_root(self):
        r = self.r
        t = r.choice(VT)
        if r.random() < 0.15:
            # end on a mask converted back to integers
            w = t[0]
            m = self.build_cmp((w, t[1]), r.randint(1, 2))
            return {"k": "frommask", "w": w, "m": m}
        return self.build_vec(t, r.randint(1, 3))

    # --- RPN emission (the oracle evaluates at 128/w lanes) ---

    def rpn(self, n, out):
        k = n["k"]
        if k == "load":
            w, s = n["t"]
            out.append({"k": "vpush", "w": w, "s": s,
                        "v": [v % (1 << w) for v in self.tables[n["t"]]]})
        elif k == "bcast":
            w, s = n["t"]
            out.append({"k": "vbcast", "w": w, "s": s, "v": n["v"] % (1 << w)})
        elif k == "bin":
            self.rpn(n["a"], out)
            self.rpn(n["b"], out)
            op = {"Sub": "sub", "And": "and", "Or": "or", "Xor": "xor",
                  "AndNot": "andnot", "Min": "min", "Max": "max"}.get(n["op"], n["op"].lower())
            out.append({"k": "vbin", "op": op})
        elif k == "shift":
            self.rpn(n["a"], out)
            out.append({"k": "vshift", "op": "shl" if n["op"] == "ShiftAllLeft" else "shr",
                        "c": n["c"]})
        elif k == "rot":
            self.rpn(n["a"], out)
            out.append({"k": "vrot", "c": n["c"] % (1 << 64)})
        elif k == "cmp":
            self.rpn(n["a"], out)
            self.rpn(n["b"], out)
            op = {"Equal": "eq", "NotEqual": "ne", "Less": "lt",
                  "LessEqual": "le", "Greater": "gt", "GreaterEqual": "ge"}[n["op"]]
            out.append({"k": "vcmp", "op": op})
        elif k == "mbin":
            self.rpn(n["a"], out)
            self.rpn(n["b"], out)
            out.append({"k": "mbin", "op": {"And": "and", "Or": "or", "Xor": "xor",
                                            "Equal": "eq"}[n["op"]]})
        elif k == "mun":
            self.rpn(n["a"], out)
            out.append({"k": "mun", "op": "not"})
        elif k == "sel":
            # IfElse(mask, x, y): the stack order is mask, x, y then vsel
            self.rpn(n["m"], out)
            self.rpn(n["a"], out)
            self.rpn(n["b"], out)
            out.append({"k": "vsel"})
        elif k == "masked":
            self.rpn(n["m"], out)
            self.rpn(n["a"], out)
            out.append({"k": "vmasked"})
        elif k == "tomask":
            self.rpn(n["a"], out)
            out.append({"k": "vtomask"})
        elif k == "frommask":
            self.rpn(n["m"], out)
            out.append({"k": "vfrommask", "w": n["w"]})
        else:
            raise ValueError(k)

    # --- Go rendering (same chains as simd package code) ---

    def go(self, n):
        k = n["k"]
        T = lambda t: f"simd.{GONAME[t]}"
        if k == "load":
            t = n["t"]
            return f"simd.Load{GONAME[t]}(g_{ELEM[t]})"
        if k == "bcast":
            t = n["t"]
            v = n["v"]
            if t[1]:
                sv = v - (1 << t[0]) if v >= (1 << (t[0] - 1)) else v
            else:
                sv = v
            return f"simd.Broadcast{GONAME[t]}({ELEM[t]}({sv}))"
        if k == "bin":
            return f"({self.go(n['a'])}.{n['op']}({self.go(n['b'])}))"
        if k == "shift":
            return f"({self.go(n['a'])}.{n['op']}({n['c']}))"
        if k == "rot":
            return f"({self.go(n['a'])}.RotateAllLeft({n['c']}))"
        if k == "cmp":
            return f"({self.go(n['a'])}.{n['op']}({self.go(n['b'])}))"
        if k == "mbin":
            return f"({self.go(n['a'])}.{n['op']}({self.go(n['b'])}))"
        if k == "mun":
            return f"({self.go(n['a'])}.Not())"
        if k == "sel":
            return f"({self.go(n['a'])}.IfElse({self.go(n['m'])}, {self.go(n['b'])}))"
        if k == "masked":
            return f"({self.go(n['a'])}.Masked({self.go(n['m'])}))"
        if k == "tomask":
            return f"({self.go(n['a'])}.ToMask())"
        if k == "frommask":
            return f"({self.go(n['m'])}.ToInt{n['w']}s())"
        raise ValueError(k)

    def result_type(self, n):
        """The (w, s) of the chain's result, for the checksum loop."""
        k = n["k"]
        if k in ("load", "bcast"):
            return n["t"]
        if k in ("bin", "shift", "rot", "sel", "masked"):
            return n["t"]
        if k == "frommask":
            return (n["w"], True)
        raise ValueError(k)


GOHEADER = '''package main

import (
	"fmt"
	"simd"
)

func hash(h uint64, v uint64) uint64 { return (h ^ v) * 1099511628211 }
'''


def program(seed, n):
    global AVAIL
    AVAIL = load_avail()
    r = random.Random(seed)
    g = Gen(r)
    trees = [g.build_root() for _ in range(n)]
    recs = []
    src = GOHEADER
    for t in g.tables.values():
        pass
    for w, s in VT:
        vals = g.tables[(w, s)]
        src += f"var g_{ELEM[(w, s)]} = []{ELEM[(w, s)]}{{" + ", ".join(str(v) for v in vals) + "}\n"
    for i, tree in enumerate(trees):
        ops = []
        g.rpn(tree, ops)
        recs.append({"e": i, "ops": ops})
        w, sg = g.result_type(tree)
        lanes = min(4, 128 // w)
        # the checksum mirrors the oracle: FNV-1a over the first lanes,
        # each lane reinterpreted as unsigned at its width
        cast = f"uint{w}" if w < 64 else "uint64"
        src += (f"\n//go:noinline\nfunc f{i}() uint64 {{\n"
                f"\tvar s [64]{ELEM[(w, sg)]}\n"
                f"\t{g.go(tree)}.Store(s[:])\n"
                f"\th := uint64(1469598103934665603)\n"
                f"\tfor j := 0; j < {lanes}; j++ {{\n"
                f"\t\th = hash(h, uint64({cast}(s[j])))\n"
                f"\t}}\n"
                f"\treturn h\n}}\n")
    src += "\nfunc main() {\n"
    for i in range(len(trees)):
        src += f"\tfmt.Printf(\"expr {i}: %#x\\n\", f{i}())\n"
    src += "}\n"
    return recs, src


def run(seed, n, out):
    os.makedirs(out, exist_ok=True)
    gomod = os.path.join(out, "gomain")
    os.makedirs(gomod, exist_ok=True)
    recs, src = program(seed, n)
    open(os.path.join(out, "exprs.json"), "w").write(json.dumps(recs))
    open(os.path.join(gomod, "main.go"), "w").write(src)
    open(os.path.join(gomod, "go.mod"), "w").write("module sorc\ngo 1.28\n")
    gobin = os.environ.get("GO", "go")
    env = dict(os.environ, GOEXPERIMENT="simd", GOTOOLCHAIN="local",
               GODEBUG=os.environ.get("GODEBUG_S", "simd=128"))
    gout = subprocess.run([gobin, "run", "."], cwd=gomod, capture_output=True,
                          text=True, env=env, timeout=600)
    if gout.returncode != 0:
        return f"seed {seed}: go run failed: {gout.stderr[:400]}"
    obin = os.environ.get("ORACLE_SIMD", "lake exe oracle-simd")
    import shlex
    cmd = shlex.split(obin) + [os.path.abspath(os.path.join(out, "exprs.json"))]
    lout = subprocess.run(cmd, capture_output=True, text=True, timeout=600,
                         cwd=os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    if lout.returncode != 0:
        return f"seed {seed}: oracle failed: {lout.stdout[:200]} {lout.stderr[:300]}"
    gl, ll = gout.stdout.splitlines(), lout.stdout.splitlines()
    if len(gl) != len(ll):
        return f"seed {seed}: LINE COUNT {len(gl)} vs {len(ll)}"
    diffs = [(a, b) for a, b in zip(gl, ll) if a != b]
    if diffs:
        return f"seed {seed}: {len(diffs)} DIFFS\n" + "\n".join(
            f"  go  : {a}\n  lean: {b}" for a, b in diffs[:5])
    return f"seed {seed}: {len(gl)} chains OK"


def main():
    if len(sys.argv) != 4:
        print(__doc__)
        raise SystemExit(2)
    print(run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]))


if __name__ == "__main__":
    main()
