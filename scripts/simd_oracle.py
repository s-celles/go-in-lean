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

Usage: simd_oracle.py SEED N OUTDIR [--float]
  --float roots every chain in Float64s and weights MulAdd up, targeting
    the fused/unfused boundary of golang/go#80355 on the emulated paths.
Environment: GO (toolchain under test, default "go"), ORACLE_SIMD (default
  the lake exe), GODEBUG_S (default "simd=128").
"""
import json, os, random, subprocess, sys

# (width, signed) for the integer vector types; masks follow the width.
# "f64" is the float64 vector type; its lanes are IEEE bit patterns.
F64 = "f64"
VT = [(w, s) for w in (8, 16, 32, 64) for s in (False, True)] + [F64]

import struct as _struct
def fbits(v):
    return _struct.unpack("<Q", _struct.pack("<d", v))[0]

# finite values only: the amd64 Min/Max NaN deviation is documented, and the
# MulAdd fusion (golang/go#80355) is the target of this step
# -0.0 is excluded: the amd64 Max/Min +-0 result deviates from the documented
# semantics (the stubs table documents it), and the divergence is already
# understood; the hunt targets the MulAdd fusion (golang/go#80355)
FPOOL = [0.0, 0.1, -0.1, 0.5, 1.5, 2.5, -2.5, 1e300, -1e300, 1e-310,
         -(1e-310), 1.0 + 2.0 ** -52, -(1.0 + 2.0 ** -52), 2.0 ** 53,
         0.49999999999999994, 3.141592653589793, 4503599627370496.5,
         1.0 + 2.0 ** -51, 16777217.0, 1e10]
GONAME = {(w, sg): f"{'Uint' if not sg else 'Int'}{w}s" for w in (8, 16, 32, 64) for sg in (False, True)}
GONAME[F64] = "Float64s"

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

    def __init__(self, r, float_mode=False):
        self.r = r
        # --float: every chain roots in Float64s and MulAdd is weighted up,
        # so the campaigns target the fused/unfused boundary of #80355
        self.float_mode = float_mode
        self.tables = {t: table(t[0], t[1]) for t in VT if t != F64}
        self.tables[F64] = FPOOL

    def leaf(self, t):
        r = self.r
        if r.random() < 0.5:
            # Load from the fixed table - the RPN carries the same lanes
            return {"k": "load", "t": t}
        if t == F64:
            v = fbits(r.choice(FPOOL))
            return {"k": "bcast", "t": t, "v": v}
        v = lane_pool(t[0], t[1], r)
        return {"k": "bcast", "t": t, "v": v}

    def build_vec(self, t, d):
        r = self.r
        if d <= 0 or r.random() < 0.35:
            return self.leaf(t)
        if t == F64:
            return self.build_f64(d)
        w, s = t
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

    def build_f64(self, d):
        """Float64 chains: Add/Sub/Mul/Min/Max/MulAdd/Abs/Neg/comparisons, plus
        IfElse/Masked through the width-64 masks."""
        r = self.r
        t = F64
        if d <= 0 or r.random() < 0.35:
            return self.leaf(t)
        av = AVAIL.get(GONAME[t], set())
        x = r.random()
        if x < 0.45:
            ops = [o for o in ("Add", "Sub", "Mul", "Min", "Max") if o in av]
            if ops:
                op = r.choice(ops)
                return {"k": "fbin", "op": op, "t": t,
                        "a": self.build_f64(d - 1), "b": self.build_f64(d - 1)}
        if x < (0.80 if self.float_mode else 0.65) and "MulAdd" in av:
            return {"k": "fma", "t": t,
                    "a": self.build_f64(d - 1), "b": self.build_f64(d - 1), "c": self.build_f64(d - 1)}
        if x < 0.75:
            op = r.choice([o for o in ("Abs", "Neg") if o in av])
            return {"k": "fun", "op": op, "t": t, "a": self.build_f64(d - 1)}
        if x < 0.88 and "IfElse" in av:
            m = self.build_fcmp(d)
            return {"k": "sel", "t": t, "m": m,
                    "a": self.build_f64(d - 1), "b": self.build_f64(d - 1)}
        if "Masked" in av:
            m = self.build_fcmp(d)
            return {"k": "masked", "t": t, "m": m, "a": self.build_f64(d - 1)}
        return self.build_f64(d)

    def build_fcmp(self, d):
        """A mask of width 64 from float comparisons (or mask algebra)."""
        r = self.r
        t = F64
        if d <= 0 or r.random() < 0.6:
            av = AVAIL.get(GONAME[t], set())
            ops = [o for o in ("Equal", "NotEqual", "Less", "LessEqual", "Greater", "GreaterEqual") if o in av]
            op = r.choice(ops or ["Equal"])
            return {"k": "fcmp", "op": op, "w": 64,
                    "a": self.build_f64(d - 1), "b": self.build_f64(d - 1)}
        x = r.random()
        if x < 0.5:
            op = r.choice(["And", "Or", "Xor", "Equal"])
            return {"k": "mbin", "op": op, "w": 64,
                    "a": self.build_fcmp(d - 1), "b": self.build_fcmp(d - 1)}
        if x < 0.75:
            return {"k": "mun", "w": 64, "a": self.build_fcmp(d - 1)}
        av = AVAIL.get(GONAME[F64], set())
        ops = [o for o in ("Equal", "NotEqual", "Less", "LessEqual", "Greater", "GreaterEqual") if o in av]
        op = r.choice(ops or ["Equal"])
        return {"k": "fcmp", "op": op, "w": 64,
                "a": self.build_f64(d - 1), "b": self.build_f64(d - 1)}

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
        if self.float_mode:
            return self.build_f64(r.randint(1, 3))
        t = r.choice(VT)
        if t == F64:
            return self.build_f64(r.randint(1, 3))
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
            if n["t"] == F64:
                out.append({"k": "vpush", "w": 64, "s": True,
                            "v": [fbits(v) for v in self.tables[F64]]})
            else:
                w, sg = n["t"]
                out.append({"k": "vpush", "w": w, "s": sg,
                            "v": [v % (1 << w) for v in self.tables[n["t"]]]})
        elif k == "bcast":
            if n["t"] == F64:
                out.append({"k": "vbcast", "w": 64, "s": True, "v": n["v"] % (1 << 64)})
            else:
                w, sg = n["t"]
                out.append({"k": "vbcast", "w": w, "s": sg, "v": n["v"] % (1 << w)})
        elif k == "fbin":
            op = {"Add": "fadd", "Sub": "fsub", "Mul": "fmul", "Min": "fmin", "Max": "fmax"}[n["op"]]
            self.rpn(n["a"], out)
            self.rpn(n["b"], out)
            out.append({"k": "vbin", "op": op})
        elif k == "fun":
            self.rpn(n["a"], out)
            out.append({"k": "vfun", "op": "fabs" if n["op"] == "Abs" else "fneg"})
        elif k == "fma":
            self.rpn(n["a"], out)
            self.rpn(n["b"], out)
            self.rpn(n["c"], out)
            out.append({"k": "vfma"})
        elif k == "fcmp":
            op = {"Equal": "feq", "NotEqual": "fne", "Less": "flt",
                  "LessEqual": "fle", "Greater": "fgt", "GreaterEqual": "fge"}[n["op"]]
            self.rpn(n["a"], out)
            self.rpn(n["b"], out)
            out.append({"k": "vcmp", "op": op})
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
            if t == F64:
                return "simd.LoadFloat64s(g_float64)"
            return f"simd.Load{GONAME[t]}(g_{ELEM[t]})"
        if k == "fbin":
            return f"({self.go(n['a'])}.{n['op']}({self.go(n['b'])}))"
        if k == "fun":
            return f"({self.go(n['a'])}.{n['op']}())"
        if k == "fma":
            return f"({self.go(n['a'])}.MulAdd({self.go(n['b'])}, {self.go(n['c'])}))"
        if k == "fcmp":
            return f"({self.go(n['a'])}.{n['op']}({self.go(n['b'])}))"
        if k == "bcast":
            t = n["t"]
            if t == F64:
                return f"simd.BroadcastFloat64s(math.Float64frombits({n['v']}))"
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
        if k in ("fbin", "fma", "fun"):
            return n["t"]
        if k == "frommask":
            return (n["w"], True)
        raise ValueError(k)


GOHEADER = '''package main

import (
	"fmt"
	"math"
	"simd"
)

func hash(h uint64, v uint64) uint64 { return (h ^ v) * 1099511628211 }

var _ = math.Float64bits
'''


def program(seed, n, float_mode=False):
    global AVAIL
    AVAIL = load_avail()
    r = random.Random(seed)
    g = Gen(r, float_mode)
    trees = [g.build_root() for _ in range(n)]
    recs = []
    src = GOHEADER
    for t in g.tables.values():
        pass
    for t in VT:
        if t == F64:
            continue
        vals = g.tables[t]
        w, sg = t
        src += f"var g_{ELEM[(w, sg)]} = []{ELEM[(w, sg)]}{{" + ", ".join(str(v) for v in vals) + "}\n"
    src += "var g_float64 = []float64{" + ", ".join(repr(v) for v in g.tables[F64]) + "}\n"
    for i, tree in enumerate(trees):
        ops = []
        g.rpn(tree, ops)
        recs.append({"e": i, "ops": ops})
        rt = g.result_type(tree)
        if rt == F64:
            src += (f"\n//go:noinline\nfunc f{i}() uint64 {{\n"
                    f"\tvar s [64]float64\n"
                    f"\t{g.go(tree)}.Store(s[:])\n"
                    f"\th := uint64(1469598103934665603)\n"
                    f"\tfor j := 0; j < 2; j++ {{\n"
                    f"\t\tv := math.Float64bits(s[j])\n"
                    f"\t\t// NaN payloads are unspecified: canonicalize like the oracle\n"
                    f"\t\tif v&0x7FF0000000000000 == 0x7FF0000000000000 && v&0xFFFFFFFFFFFFF != 0 {{\n"
                    f"\t\t\tv = 0x7FF8000000000001\n"
                    f"\t\t}}\n"
                    f"\t\th = hash(h, v)\n"
                    f"\t}}\n"
                    f"\treturn h\n}}\n")
            continue
        w, sg = rt
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


def run(seed, n, out, float_mode=False):
    os.makedirs(out, exist_ok=True)
    gomod = os.path.join(out, "gomain")
    os.makedirs(gomod, exist_ok=True)
    recs, src = program(seed, n, float_mode)
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
    args = [a for a in sys.argv[1:] if a == "--float"]
    rest = [a for a in sys.argv[1:] if a != "--float"]
    if len(rest) != 3:
        print(__doc__)
        raise SystemExit(2)
    print(run(int(rest[0]), int(rest[1]), rest[2], bool(args)))


if __name__ == "__main__":
    main()
