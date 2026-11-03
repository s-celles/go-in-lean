#!/usr/bin/env python3
"""Metamorphic fuzzer for floating-point arithmetic, conversions and math intrinsics.

Each random expression is compiled three ways, as in metamorphic_fuzz.py:
  c<i>  constants injected as math.Float64frombits(0x...)/Float32frombits (calls the SSA
        backend folds on the build host with IEEE semantics; NOT Go constant expressions,
        whose exact evaluation would legitimately differ from run-time rounding);
  v<i>  the same constants passed as run-time parameters;
  h<i>  an inlined helper with constant arguments.
Results are compared bit-exactly after NaN canonicalisation (NaN payloads are unspecified).
With --late, a fourth version l<i> injects every constant as bytes loaded from the
read-only string lateS (lateS[i] == i) recombined with shifts and ORs: the generic
optimiser cannot fold the loads, the arch lowering can (symIsRO), so architecture-
specific constant-folding rules - conversions with double rounding, float op folds -
see the value in the lower phase only (the class of golang/go#82775).

False positives avoided by construction:
  * every float * / + - result is wrapped in an explicit conversion, which forbids FMA fusion
    (Go spec: an explicit conversion rounds and prevents fusion);
  * float->int conversions go through a range guard (out-of-range results are implementation-
    defined); the guard is inlined, so all three versions convert the same in-range value;
  * signed zero and NaN constants are injected by bit pattern, so -0 is preserved.
Targets: int<->float conversions (int64->float32 double rounding, uint64 conversions on
32-bit ports), float32<->float64, Sqrt/Abs/Floor/Ceil/Trunc/Round/RoundToEven/Copysign/FMA/Max/Min
intrinsics, whose lowering is architecture-specific.
Usage: float_fuzz.py SEED N OUTDIR [--canary]
"""
import os, random, re, struct, subprocess, sys

LATE = "--late" in sys.argv

def late_u64(v):
    """The uint64 v as bytes of the read-only string lateS (lateS[i] == i), ORed together:
    a value the generic optimiser cannot fold but the arch lowering can (symIsRO)."""
    parts = [f"uint64(lateS[{(v >> 8 * i) & 0xFF}])" + (f"<<{8 * i}" if i else "")
             for i in range(8) if (v >> 8 * i) & 0xFF]
    if not parts:
        return "uint64(lateS[0])"
    return "(" + " | ".join(parts) + ")"


def f64bits(v):  return struct.unpack("<Q", struct.pack("<d", v))[0]
def f32bits(v):  return struct.unpack("<I", struct.pack("<f", v))[0]

F64 = [0.0, 1.0, -1.0, 0.5, 1.5, 2.5, -2.5, 3.5, -0.5, 0.1, 1e300, -1e300, 1e-310, 4503599627370496.5,
       2.0**52 + 0.5, 2.0**53, 2.0**53 + 2, 2.0**63, -2.0**63, 2.0**64, 2.0**31, -2.0**31 - 1, 2.0**32,
       16777217.0, 0.49999999999999994, 1.7976931348623157e308, 2.2250738585072014e-308,
       float("inf"), float("-inf")]
F64B = sorted({f64bits(v) for v in F64} | {f64bits(-0.0), 0x7ff8000000000000, 0x0000000000000001,
                                         0x8000000000000001, 0x3fefffffffffffff})
I64 = [0, 1, -1, 2, 3, 7, (1 << 24) + 1, (1 << 24) - 1, (1 << 53) + 1, (1 << 53) - 1,
       (1 << 53) + (1 << 29) + 1, (1 << 54) + (1 << 30) + 1, (1 << 62) + (1 << 38) + 1,
       (1 << 63) - 1, -(1 << 63), -(1 << 53) - (1 << 29) - 1, (1 << 31), -(1 << 31) - 1,
       (1 << 32) + 1, 0x7fffff80_00000001 - (1 << 63) * 0, 123456789123456789]
U64 = [0, 1, (1 << 63), (1 << 63) + 1, (1 << 64) - 1, (1 << 64) - 2049, (1 << 63) + (1 << 39) + 1,
       (1 << 53) + 1, (1 << 32), (1 << 64) - (1 << 40) + 1, 0x8000000000000401]

FT = ["float64", "float32"]
IT = ["int64", "uint64", "int32", "uint32", "int16", "uint16", "int8", "uint8"]
RANGE = {"int64": ("-0x1p63", "0x1p63"), "uint64": ("0", "0x1p64"), "int32": ("-0x1p31", "0x1p31"),
         "uint32": ("0", "0x1p32"), "int16": ("-0x1p15", "0x1p15"), "uint16": ("0", "0x1p16"),
         "int8": ("-0x1p7", "0x1p7"), "uint8": ("0", "0x1p8")}


class Gen:
    def __init__(self, r):
        self.r = r; self.consts = []          # (gotype, value-as-uint64-bits-or-int)

    def const(self, t):
        r = self.r
        if t == "float64":
            v = r.choice(F64B)
        elif t == "float32":
            v = f32bits(r.choice([x for x in F64 if abs(x) < 3.4e38 or x != x or abs(x) == float("inf")]))
        elif t.startswith("u"):
            v = r.choice(U64) % (1 << int(t[4:]))
        else:
            w = int(t[3:]); v = r.choice(I64); v = ((v + (1 << (w - 1))) % (1 << w)) - (1 << (w - 1))
        self.consts.append((t, v))
        return ("k", len(self.consts) - 1, t)

    def leaf(self, t):
        if self.r.random() < 0.5:
            return self.const(t)
        return ("var", t)

    def expr(self, t, d):
        r = self.r
        if d <= 0 or r.random() < 0.25:
            return self.leaf(t)
        if t in FT:
            k = r.random()
            if k < 0.30:
                return ("fbin", r.choice("+-*/"), self.expr(t, d - 1), self.expr(t, d - 1), t)
            if k < 0.55:
                fn = r.choice(["Sqrt", "Abs", "Floor", "Ceil", "Trunc", "Round", "RoundToEven"])
                return ("mf1", fn, self.expr(t, d - 1), t)
            if k < 0.65:
                fn = r.choice(["Copysign", "Max", "Min"])
                return ("mf2", fn, self.expr(t, d - 1), self.expr(t, d - 1), t)
            if k < 0.70:
                return ("fma", self.expr(t, d - 1), self.expr(t, d - 1), self.expr(t, d - 1), t)
            src = r.choice(IT + FT)
            return ("conv", t, self.expr(src, d - 1))
        # integer result: a guarded conversion from a float, or an int conversion
        if r.random() < 0.7:
            return ("f2i", t, self.expr(r.choice(FT), d - 1))
        return ("conv", t, self.expr(r.choice(IT), d - 1))


def render(e, mode, intype):
    tag = e[0]
    if tag == "var":
        t = e[1]
        return f"{t}(x)" if intype != t else "x"
    if tag == "k":
        t, v = mode["consts"][e[1]], mode["vals"][e[1]]
        if mode.get("late"):
            u = late_u64(v)
            if t == "float64":
                return f"math.Float64frombits({u})"
            if t == "float32":
                return f"math.Float32frombits(uint32({u}))"
            return f"{t}({u})"
        if t == "float64":
            return f"math.Float64frombits({v:#x})" if mode["const"] else f"math.Float64frombits(k{e[1]})"
        if t == "float32":
            return f"math.Float32frombits({v:#x})" if mode["const"] else f"math.Float32frombits(uint32(k{e[1]}))"
        return f"{t}({v})" if mode["const"] else f"{t}(k{e[1]})"
    if tag == "fbin":
        return f"{e[4]}({render(e[2], mode, intype)} {e[1]} {render(e[3], mode, intype)})"
    if tag == "mf1":
        a = render(e[2], mode, intype)
        return f"math.{e[1]}({a})" if e[3] == "float64" else f"float32(math.{e[1]}(float64({a})))"
    if tag == "mf2":
        a, b = render(e[2], mode, intype), render(e[3], mode, intype)
        return f"math.{e[1]}({a}, {b})" if e[4] == "float64" else f"float32(math.{e[1]}(float64({a}), float64({b})))"
    if tag == "fma":
        a, b, c = (render(x, mode, intype) for x in e[1:4])
        return f"math.FMA({a}, {b}, {c})" if e[4] == "float64" else f"float32(math.FMA(float64({a}), float64({b}), float64({c})))"
    if tag == "conv":
        return f"{e[1]}({render(e[2], mode, intype)})"
    if tag == "f2i":
        return f"cvt_{e[1]}(float64({render(e[2], mode, intype)}))"
    raise ValueError(tag)


HEADER = '''package main

import (
	"fmt"
	"math"
	"os"
)

var _ = math.Abs

var bad = 0

func report(i int, kind string, x, got, want uint64) {
	bad++
	if bad <= 30 {
		fmt.Printf("expr %d (%s): x=%#x got %#x want %#x\\n", i, kind, x, got, want)
	}
}

func cf64(f float64) uint64 {
	if f != f {
		return 0x7ff8000000000001
	}
	return math.Float64bits(f)
}

func cf32(f float32) uint64 {
	if f != f {
		return 0x7fc00001
	}
	return uint64(math.Float32bits(f))
}
'''


def guards():
    out = []
    for t in IT:
        lo, hi = RANGE[t]
        cmp_lo = f"f >= {lo}" if lo != "0" else "f >= 0"
        out.append(f"func cvt_{t}(f float64) {t} {{\n\tif {cmp_lo} && f < {hi} {{\n\t\treturn {t}(f)\n\t}}\n\treturn 0\n}}\n")
    return "\n".join(out)


def canon(t, s):
    if t == "float64": return f"cf64({s})"
    if t == "float32": return f"cf32({s})"
    return f"uint64({s})"


INPUTS = {
    "float64": [f"math.Float64frombits({b:#x})" for b in F64B],
    "int64": [str(v) for v in I64],
    "uint64": [str(v) for v in U64],
}

LATE_S = '"' + "".join(f"\\x{b:02x}" for b in range(256)) + '"'


def program(seed, n, drop, canary=False):
    r = random.Random(seed)
    src = HEADER + guards()
    if LATE:
        src += f"\nconst lateS = {LATE_S}\nvar _ = lateS\n"
    checks = []
    for i in range(n):
        g = Gen(r)
        intype = r.choice(["float64", "int64", "uint64"])
        rt = r.choice(FT + ["int64", "uint64", "int32", "uint8"])
        e = g.expr(rt, r.randint(1, 3))
        if i in drop:
            continue
        if canary and i == 0:
            # Sensitivity check: the const version uses a Go constant expression (exact), the
            # others round at run time, so 0.1*3 differs (0.3 vs 0.30000000000000004).
            src += ("//go:noinline\nfunc c0(x float64) uint64 { return cf64(0.1 * 3) }\n"
                    "//go:noinline\nfunc v0(x float64, k0, k1 uint64) uint64 { return cf64(float64(math.Float64frombits(k0) * math.Float64frombits(k1))) }\n"
                    "func hh0(x float64, k0, k1 uint64) uint64 { return cf64(float64(math.Float64frombits(k0) * math.Float64frombits(k1))) }\n"
                    "//go:noinline\nfunc h0(x float64) uint64 { return hh0(x, 0x3fb999999999999a, 0x4008000000000000) }\n")
            checks.append("\tfor _, x := range []float64{0} {\n\t\tvv := v0(x, 0x3fb999999999999a, 0x4008000000000000)\n"
                          "\t\tif cc := c0(x); cc != vv { report(0, \"const\", 0, cc, vv) }\n\t}\n")
            continue
        consts = [t for t, _ in g.consts]; vals = [v for _, v in g.consts]
        cm = {"const": True, "consts": consts, "vals": vals}
        vm = {"const": False, "consts": consts, "vals": vals}
        lm = {"const": False, "late": True, "consts": consts, "vals": vals}
        params = "".join(f", k{j} uint64" for j in range(len(consts)))
        args = "".join(f", uint64({v:#x})" if t in FT else f", uint64({t}({v}))" for t, v in g.consts)
        src += (f"//go:noinline\nfunc c{i}(x {intype}) uint64 {{ return {canon(rt, render(e, cm, intype))} }}\n"
                f"//go:noinline\nfunc v{i}(x {intype}{params}) uint64 {{ return {canon(rt, render(e, vm, intype))} }}\n"
                f"func hh{i}(x {intype}{params}) uint64 {{ return {canon(rt, render(e, vm, intype))} }}\n"
                f"//go:noinline\nfunc h{i}(x {intype}) uint64 {{ return hh{i}(x{args}) }}\n")
        if LATE:
            src += f"//go:noinline\nfunc l{i}(x {intype}) uint64 {{ return {canon(rt, render(e, lm, intype))} }}\n"
        vargs = "".join(f", uint64({v:#x})" if t in FT else f", uint64({t}({v}))" for t, v in g.consts)
        xs = ", ".join(INPUTS[intype])
        xv = "math.Float64bits(x)" if intype == "float64" else "uint64(x)"
        checks.append(f"\tfor _, x := range []{intype}{{{xs}}} {{\n"
                      f"\t\tvv := v{i}(x{vargs})\n"
                      f"\t\tif cc := c{i}(x); cc != vv {{ report({i}, \"const\", {xv}, cc, vv) }}\n"
                      f"\t\tif hv := h{i}(x); hv != vv {{ report({i}, \"inline\", {xv}, hv, vv) }}\n"
                      + (f"\t\tif lv := l{i}(x); lv != vv {{ report({i}, \"late\", {xv}, lv, vv) }}\n" if LATE else "")
                      + "\t}\n")
    src += "\nfunc main() {\n" + "".join(checks)
    src += ('\tfmt.Printf("seed %d: %d expressions, %d mismatches\\n", ' + f"{seed}, {n - len(drop)}" +
            ', bad)\n\tif bad > 0 {\n\t\tos.Exit(1)\n\t}\n}\n')
    return src


def main():
    argv = [a for a in sys.argv[1:] if not a.startswith("--")]
    seed, n, out = int(argv[0]), int(argv[1]), argv[2]
    canary = "--canary" in sys.argv
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, "go.mod"), "w").write("module ffuzz\ngo 1.25\n")
    gobin = os.environ.get("GO", "go")
    drop = set()
    for _ in range(30):
        src = program(seed, n, drop, canary)
        open(os.path.join(out, "main.go"), "w").write(src)
        rr = subprocess.run([gobin, "build", "-gcflags=-e", "-o", os.devnull, "."], cwd=out,
                            capture_output=True, text=True)
        if rr.returncode == 0:
            break
        lines = src.splitlines(); newly = set()
        for m in re.finditer(r"main\.go:(\d+):", rr.stderr):
            for j in range(int(m.group(1)) - 1, -1, -1):
                mm = re.match(r"func (?:c|v|hh|h|l)(\d+)\(", lines[j]) or re.search(r"\b[vchl](\d+)\(x", lines[j])
                if mm:
                    newly.add(int(mm.group(1))); break
        if not newly:
            raise SystemExit("cannot fix compile errors:\n" + rr.stderr[:2000])
        drop |= newly
    else:
        raise SystemExit("compile errors remain after 30 rounds")
    print(f"seed {seed}: {n - len(drop)} expressions ({len(drop)} dropped)")


if __name__ == "__main__":
    main()
