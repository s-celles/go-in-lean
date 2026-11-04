#!/usr/bin/env python3
"""Differential fuzzer for the goexperiment.simd package (src/simd).

The upstream suites test single operations against scalar helpers (simd_test.go)
and exhaustively per architecture (simd/archsimd/internal/simd_test). Not
covered: composed chains of operations, the methods upstream marks TODO
(IfElse, Masked, ToMask, ToBits, Not, saturations, reshapes), and agreement
between the hardware lowerings of different architectures and vector sizes.

Each generated program builds N chains of SIMD operations over the portable
simd API (types, arities and results parsed from simd_stubs.go, so the table
follows the tree), loads inputs from fixed literal tables and folds each chain
into a checksum over the first four lanes (vectors are >=128 bits everywhere,
so the first four lanes are identical on every configuration; only
lane-independent operations are generated). The oracle is cross-configuration
agreement: the campaign runs the same program natively (auto size), with
GODEBUG=simd=0/128/256/512 (emulated and forced hardware sizes) and on other
GOARCHes (arm64 Neon, emulated ports) - a configuration that disagrees has a
bug in its lowering, or an operation whose semantics vary (triage: MulAdd
fusion and float Min/Max NaN handling are the known suspects).

Usage: simd_fuzz.py SEED N OUTDIR
"""
import os, random, re, subprocess, sys

VT = ["Int8s", "Uint8s", "Int16s", "Uint16s", "Int32s", "Uint32s",
      "Int64s", "Uint64s", "Float32s", "Float64s"]
MT = ["Mask8s", "Mask16s", "Mask32s", "Mask64s"]
# Non-lane ops, panicky ops, arch-dependent reductions, untested I/O helpers.
EXCLUDE = {"String", "Len", "Store", "StorePart", "ToArch", "TrailingZeros"}
# Documented cross-configuration divergences (simd_stubs.go): amd64 Max/Min are
# non-commutative on NaN/+/-Inf (IEEE 754-2019 says NaN), and MulAdd is unfused
# on wasm and in the emulated bridge (golang/go#80355).
EXCLUDE_BY_TYPE = {"Float32s": {"Min", "Max", "MulAdd"}, "Float64s": {"Min", "Max", "MulAdd"}}

ELEM = {"Int8s": "int8", "Uint8s": "uint8", "Int16s": "int16", "Uint16s": "uint16",
        "Int32s": "int32", "Uint32s": "uint32", "Int64s": "int64", "Uint64s": "uint64",
        "Float32s": "float32", "Float64s": "float64"}


def width(t):
    return int(re.search(r"(\d+)", t).group(1))


def load_stubs():
    goroot = os.environ.get("GOROOT")
    if not goroot:
        goroot = subprocess.run([os.environ.get("GO", "go"), "env", "GOROOT"],
                                 capture_output=True, text=True).stdout.strip()
    path = os.path.join(goroot, "src", "simd", "simd_stubs.go")
    ops, load, bcast = {}, {}, {}
    meth = re.compile(r"^func \(x (\w+)\) (\w+)\(([^)]*)\) \(z (\w+)\)")
    fn = re.compile(r"^func (Load|Broadcast)(\w+)\([^)]*\) \(z (\w+)\)")
    for line in open(path):
        m = meth.match(line)
        if m:
            recv, name, params, res = m.groups()
            if (name not in EXCLUDE and res in VT + MT
                    and name not in EXCLUDE_BY_TYPE.get(recv, ())):
                params = [p.strip().split()[-1] for p in params.split(",")] if params.strip() else []
                ops.setdefault(recv, []).append((name, params, res))
            continue
        m = fn.match(line)
        if m:
            kind, t, res = m.groups()
            if res in VT and t in VT:
                (load if kind == "Load" else bcast)[res] = kind + t
    return ops, load, bcast


def num_lit(r, t):
    """A Go expression for an interesting scalar constant of element type t."""
    w = width(t)
    if t == "Float64s":
        return r.choice(["0.0", "-0.0", "1.0", "-1.0", "0.5", "-0.5", "2.5", "-2.5",
                        "1e300", "-1e300", "1.5", "4503599627370496.5", "1e-310",
                        "3.141592653589793", "math.Inf(1)", "math.Inf(-1)", "math.NaN()"])
    if t == "Float32s":
        return r.choice(["0.0", "-0.0", "1.0", "-1.0", "0.5", "-0.5", "2.5", "-2.5",
                         "16777217.0", "1e30", "-1e30", "3.140625",
                         "math.Inf(1)", "math.Inf(-1)", "math.NaN()"])
    if t[0] == "U":
        hi = (1 << w) - 1 if w < 64 else (1 << 64) - 1
        return r.choice(["0", "1", "2", "3", "7", str(hi), str(hi - 1), str(hi // 2 + 1),
                         str(1 << (w - 1)) if w < 64 else "9223372036854775808", "85", "170"])
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    return r.choice(["0", "1", "-1", "2", "-2", str(lo), str(hi), str(hi - 1), str(lo + 1),
                     str(hi // 2), "85", "-170"])


HEADER = '''package main

import (
	"fmt"
	"math"
	"simd"
)

func fb64(f float64) uint64 {
	if f != f {
		return 0x7ff8000000000001
	}
	return math.Float64bits(f)
}

func fb32(f float32) uint64 {
	if f != f {
		return 0x7fc00001
	}
	return uint64(math.Float32bits(f))
}

'''

I64 = [0, 1, -1, 2, -2, 3, -3, 7, -7, 120, -120, 85, -85, 170, -170,
       1 << 30, -(1 << 30), (1 << 62) + 1, -(1 << 62) - 1, 123456789, -123456789,
       0x7FFFFFFF, -0x80000000, 0x0F0F0F0F, -0x0F0F0F0F, 1 << 40, -(1 << 40),
       0x55, 0xAA, -1 << 12, 4095]


def elem_table(t):
    """A fixed input table with at least 64 elements (max lanes: 512-bit uint8)."""
    e, w = ELEM[t], width(t)
    if e == "float64":
        vals = ["0.0", "-0.0", "1.0", "-1.0", "0.5", "-0.5", "2.5", "-2.5", "0.1",
                "1e10", "-1e10", "1e300", "9007199254740992.0", "0.49999999999999994",
                "16777217.0", "math.Inf(1)", "math.Inf(-1)", "math.NaN()"]
    elif e == "float32":
        vals = ["0.0", "-0.0", "1.0", "-1.0", "0.5", "-0.5", "2.5", "-2.5", "0.1",
                "1e10", "-1e10", "1e30", "16777217.0", "3.140625",
                "float32(math.Inf(1))", "float32(math.Inf(-1))", "float32(math.NaN())"]
    elif e[0] == "u":
        vals = [str(v % (1 << w)) for v in I64] + [str((1 << w) - 1), str(1 << (w - 1))]
    else:
        vals = [str(((v + (1 << (w - 1))) % (1 << w)) - (1 << (w - 1))) for v in I64] \
            + [str((1 << (w - 1)) - 1), str(-(1 << (w - 1)))]
    while len(vals) < 64:
        vals.append(vals[len(vals) % len(vals)])
    return "[]%s{%s}" % (e, ", ".join(vals))


class Chain:
    def __init__(self, r, ops, load, bcast):
        self.r, self.ops, self.load, self.bcast = r, ops, load, bcast
        self.pool = []  # (expr, type)

    def leaf(self, t):
        r = self.r
        if r.random() < 0.5 and t in self.bcast:
            return "simd.%s(%s(%s))" % (self.bcast[t], ELEM[t], num_lit(r, t))
        return "simd.%s(g_%s)" % (self.load.get(t, "Load" + t), ELEM[t])

    def gen(self):
        r = self.r
        t = r.choice(VT)
        for _ in range(r.randint(1, 2)):
            self.pool.append((self.leaf(t), t))
        for _ in range(r.randint(2, 6)):
            self.step()
        finals = [(e, ty) for e, ty in self.pool if ty in VT]
        if not finals:
            masks = [(e, ty) for e, ty in self.pool if ty in MT] or self.pool
            e, ty = r.choice(masks)
            self.pool.append(("%s.ToInt%ds()" % (e, width(ty)), "Int%ds" % width(ty)))
            finals = self.pool[-1:]
        return r.choice(finals)

    def step(self):
        r = self.r
        cand = []
        for recv, oplist in self.ops.items():
            avail = [(e, ty) for e, ty in self.pool if ty == recv]
            for name, params, res in oplist:
                cand.extend((recv, name, params, res, ae) for ae, _ in avail)
        if not cand:
            return
        recv, name, params, res, ae = r.choice(cand)
        args = []
        for p in params:
            if p == "uint64":
                args.append(str(r.choice([0, 1, 2, 3, 7, 8, 15, 16, 31,
                                          width(res) - 1, width(res), width(res) + 1,
                                          2 * width(res)])))
                continue
            same = [(e, ty) for e, ty in self.pool if ty == p]
            if same and r.random() < 0.8:
                args.append(r.choice(same)[0])
            elif p in VT:
                args.append(self.leaf(p))
            elif p in MT:
                # Build a mask by comparing (or ToMask-ing) two vectors of that width.
                w = width(p)
                vt = r.choice([v for v in VT if width(v) == w
                               and any(n == "ToMask" for n, _, _ in self.ops.get(v, []))])
                a, b = self.leaf(vt), self.leaf(vt)
                if r.random() < 0.7:
                    cmps = [n for n, _, _ in self.ops[vt]
                            if n in ("Equal", "NotEqual", "Less", "LessEqual",
                                     "Greater", "GreaterEqual")]
                    args.append("%s.%s(%s)" % (a, r.choice(cmps), b))
                else:
                    args.append("%s.ToMask()" % a)
            else:
                return
        self.pool.append(("%s.%s(%s)" % (ae, name, ", ".join(args)), res))


def render_chain(val, t):
    """Go statements folding the first lanes of val into a checksum. Only lanes
    present on every configuration are hashed: a 128-bit vector of width-w
    elements has 128/w lanes, so hash min(4, 128/w) of them."""
    if t in MT:
        val = "%s.ToInt%ds()" % (val, width(t))
        t = "Int%ds" % width(t)
    e = ELEM[t]
    nlane = min(4, 128 // width(t))
    if e == "float64":
        lane = "fb64(s[j])"
    elif e == "float32":
        lane = "fb32(s[j])"
    elif e in ("int8", "int16", "int32", "int64"):
        lane = "uint64(uint%d(s[j]))" % width(t)
    else:
        lane = "uint64(s[j])"
    return ("\tvar s [64]%s\n\t%s.Store(s[:])\n"
            "\th := uint64(1469598103934665603)\n"
            "\tfor j := 0; j < %d; j++ {\n\t\th = (h ^ %s) * 1099511628211\n\t}\n"
            "\treturn h\n" % (e, val, nlane, lane))


def program(seed, n, drop):
    r = random.Random(seed)
    ops, load, bcast = load_stubs()
    src = HEADER
    for t in VT:
        src += "var g_%s = %s\n" % (ELEM[t], elem_table(t))
    funcs, calls = [], []
    for i in range(n):
        if i in drop:
            continue
        val, t = Chain(r, ops, load, bcast).gen()
        funcs.append("//go:noinline\nfunc f%d() uint64 {\n%s}\n" % (i, render_chain(val, t)))
        calls.append("\tfmt.Printf(\"expr %%d: %%#x\\n\", %d, f%d())" % (i, i))
    src += "\n".join(funcs)
    src += "\nfunc main() {\n" + "\n".join(calls) + "\nvar _ = fmt.Sprintf\n}\n"
    return src


def main():
    seed, n, out = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    os.makedirs(out, exist_ok=True)
    open(os.path.join(out, "go.mod"), "w").write("module sfuzz\ngo 1.28\n")
    gobin = os.environ.get("GO", "go")
    drop = set()
    for _ in range(30):
        src = program(seed, n, drop)
        open(os.path.join(out, "main.go"), "w").write(src)
        rr = subprocess.run([gobin, "build", "-gcflags=-e", "-o", os.devnull, "."],
                            cwd=out, capture_output=True, text=True,
                            env=dict(os.environ, GOEXPERIMENT="simd", GOTOOLCHAIN="local"))
        if rr.returncode == 0:
            break
        lines = src.splitlines()
        newly = set()
        for m in re.finditer(r"main\.go:(\d+):", rr.stderr):
            for j in range(int(m.group(1)) - 1, -1, -1):
                mm = re.match(r"func f(\d+)\(", lines[j])
                if mm:
                    newly.add(int(mm.group(1)))
                    break
        if not newly:
            raise SystemExit("cannot fix compile errors:\n" + rr.stderr[:2000])
        drop |= newly
    else:
        raise SystemExit("compile errors remain after 30 rounds")
    print(f"seed {seed}: {n - len(drop)} chains ({len(drop)} dropped)")


if __name__ == "__main__":
    main()
