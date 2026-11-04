#!/usr/bin/env python3
"""Lean-oracle differential fuzzer for Go integer expressions (milestone J1a).

The complementary half of GoInLean/Oracle.lean: this generator builds random
typed expression trees (the `--bits` zone of metamorphic_fuzz.py: arithmetic,
logic, shifts by constant counts, conversions, min/max, the math/bits
intrinsics, rotate) and emits, from the same IR:

* `exprs.json` - the trees in postfix (RPN) form, one record per
  (expression, input pair), for `lake exe oracle exprs.json` (the Lean model
  of Go's documented semantics, evaluated by Lean's compiler);
* `gomain/main.go` - the same expressions as Go functions over the same
  inputs, printing the same `e=<i> x=<x> y=<y> OK <n>` / `... PANIC <name>`
  lines.

The two outputs are compared line by line; a divergence is a candidate
miscompilation of the tested toolchain, triaged like any fuzzer flag. Unlike
the cross-configuration oracles, this one compares against the *documented
semantics*, so it also sees classes where every implementation is wrong
together (docs/fuzzing-vision.md, milestone J1).

Usage: oracle_bits.py SEED N OUTDIR
Environment: GO (toolchain under test, default "go"), LAKE (default "lake"),
  GOFLAGS passed through to the go command.
"""
import json, os, random, subprocess, sys

TYPES = [(w, s) for w in (8, 16, 32, 64) for s in (False, True)]
GONAME = {(w, s): f"{'u' if not s else ''}int{w}" for w in (8, 16, 32, 64) for s in (False, True)}

XPOOL = [0, 1, 2, 3, 7, 0x55, 0xAA, 0xFF, 0x7F, 0x80, 0x0F0F, 0xFFFF,
         0x7FFFFFFF, 0x80000000, 0xFFFFFFFF, 123456789, 0x123456789ABCDEF,
         (1 << 32), (1 << 40), (1 << 63), (1 << 63) - 1, (1 << 64) - 1,
         (1 << 64) - 2049, (1 << 63) + (1 << 39) + 1]
# includes pathological huge counts: the class of golang/go#82763 (constant
# counts >= 2^63 are negative int64 AuxInts in the compiler's shift rules)
COUNTS = [0, 1, 2, 3, 7, 8, 15, 16, 31, 32, 63, 64, 65, 127, 128, 255, 256,
          1 << 31, 1 << 32, 1 << 63, (1 << 63) + 2, (1 << 64) - 1]


def signed_repr(t, v):
    w, s = t
    v %= (1 << w)
    if s and v >= (1 << (w - 1)):
        return v - (1 << w)
    return v


def lit(r, t):
    w, s = t
    if s:
        lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
        v = r.choice([0, 1, -1, 2, -2, lo, hi, hi - 1, lo + 1, hi // 2, 85, -170])
    else:
        hi = (1 << w) - 1
        v = r.choice([0, 1, 2, 3, 7, hi, hi - 1, hi // 2 + 1, 1 << (w - 1), 85, 170])
    return {"k": "lit", "t": t, "v": v % (1 << w)}


class Gen:
    """Trees are typed bottom-up; `var` leaves reference x or y by name, the
    concrete values are substituted when the RPN is emitted."""

    def __init__(self, r):
        self.r = r

    def build(self, t, d):
        r = self.r
        if d <= 0 or r.random() < 0.3:
            k = r.random()
            if k < 0.45:
                return lit(r, t)
            return {"k": "var", "t": t, "which": "x" if k < 0.78 else "y"}
        w, s = t
        k = r.random()
        if k < 0.40:
            op = r.choice(["add", "sub", "mul", "and", "or", "xor", "min", "max"])
            return {"k": "bin", "op": op, "a": self.build(t, d - 1), "b": self.build(t, d - 1)}
        if k < 0.50:
            return {"k": "bin", "op": r.choice(["div", "mod"]),
                    "a": self.build(t, d - 1), "b": self.build(t, d - 1)}
        if k < 0.66:
            c = r.choice(COUNTS + [w - 1, w, w + 1, 2 * w + 1])
            return {"k": "bin", "op": r.choice(["shl", "shr"]), "a": self.build(t, d - 1),
                    "b": {"k": "lit", "t": (64, False), "v": c}}
        if k < 0.74:
            return {"k": "un", "op": r.choice(["neg", "com"]), "a": self.build(t, d - 1)}
        if k < 0.84:
            return {"k": "conv", "t": t, "a": self.build(r.choice(TYPES), d - 1)}
        if k < 0.94:
            # math/bits intrinsics, only where the result type matches t
            if t == (64, True):
                op, iw = r.choice(["oc", "lz", "tz", "len"]), r.choice([8, 16, 32, 64])
            elif not s:
                op, iw = ("rb", w) if (w >= 16 and r.random() < 0.5) else ("rev", w)
            else:
                return self.build(t, d)
            return {"k": "bits", "op": op, "w": iw, "a": self.build((iw, False), d - 1)}
        if not s:
            kk = r.choice([0, 1, 2, 3, 7, w - 1, w, -1, -3, -w])
            return {"k": "rot", "w": w, "a": self.build((w, False), d - 1),
                    "c": {"k": "lit", "t": (64, True), "v": kk % (1 << 64)}}
        return self.build(t, d)

    def rpn(self, n, x, y, out):
        k = n["k"]
        if k == "lit":
            w, s = n["t"]
            out.append({"k": "push", "w": w, "s": s, "v": n["v"]})
        elif k == "var":
            w, s = n["t"]
            v = x if n["which"] == "x" else y
            out.append({"k": "push", "w": w, "s": s, "v": v % (1 << w)})
        elif k == "un":
            self.rpn(n["a"], x, y, out)
            out.append({"k": "un", "op": n["op"]})
        elif k == "bin":
            self.rpn(n["a"], x, y, out)
            self.rpn(n["b"], x, y, out)
            out.append({"k": "bin", "op": n["op"]})
        elif k == "conv":
            self.rpn(n["a"], x, y, out)
            w, s = n["t"]
            out.append({"k": "conv", "w": w, "s": s})
        elif k == "bits":
            self.rpn(n["a"], x, y, out)
            out.append({"k": "bits", "op": n["op"], "w": n["w"]})
        elif k == "rot":
            self.rpn(n["a"], x, y, out)
            self.rpn(n["c"], x, y, out)
            out.append({"k": "rot", "w": n["w"]})
        else:
            raise ValueError(k)

    def go(self, n, cn):
        k = n["k"]
        gt = GONAME[n["t"]] if "t" in n else None
        if k == "lit":
            return cn[id(n)]
        if k == "var":
            return f"{gt}({n['which']})"
        if k == "un":
            a = self.go(n["a"], cn)
            return f"(-{a})" if n["op"] == "neg" else f"(^{a})"
        if k == "bin":
            a, b = self.go(n["a"], cn), self.go(n["b"], cn)
            op = n["op"]
            if op in ("shl", "shr"):
                sym = "<<" if op == "shl" else ">>"
                return f"({a} {sym} {b})"
            if op in ("min", "max"):
                return f"{op}({a}, {b})"
            sym = {"add": "+", "sub": "-", "mul": "*", "and": "&", "or": "|",
                   "xor": "^", "div": "/", "mod": "%"}[op]
            return f"({a} {sym} {b})"
        if k == "conv":
            return f"{gt}({self.go(n['a'], cn)})"
        if k == "bits":
            fn = {"oc": "OnesCount", "lz": "LeadingZeros", "tz": "TrailingZeros",
                  "len": "Len", "rev": "Reverse", "rb": "ReverseBytes"}[n["op"]] + str(n["w"])
            wrap = "int64(" if n["op"] in ("oc", "lz", "tz", "len") else ""
            return f"{wrap}bits.{fn}({self.go(n['a'], cn)}){')' if wrap else ''}"
        if k == "rot":
            return (f"bits.RotateLeft{n['w']}({self.go(n['a'], cn)}, "
                    f"int({cn[id(n['c'])]}))")
        raise ValueError(k)


GOHEADER = '''package main

import (
	"fmt"
	"math/bits"
	"strings"
)

func panicName(e any) string {
	s := fmt.Sprint(e)
	switch {
	case strings.Contains(s, "divide by zero"):
		return "divideError"
	case strings.Contains(s, "negative shift"):
		return "negativeShift"
	}
	return "other"
}

var _ = bits.OnesCount
'''


def program(seed, n, npair):
    r = random.Random(seed)
    g = Gen(r)
    trees = [g.build(r.choice(TYPES), r.randint(1, 3)) for _ in range(n)]
    pairs = [(r.choice(XPOOL), r.choice(XPOOL)) for _ in range(npair)]
    recs = []
    for i, tree in enumerate(trees):
        for (x, y) in pairs:
            ops = []
            g.rpn(tree, x, y, ops)
            recs.append({"e": i, "x": x, "y": y, "ops": ops})
    src = GOHEADER
    for i, tree in enumerate(trees):
        # every literal becomes a run-time variable, so no subexpression is a
        # constant expression (constant -x, x/0 and x<<w are compile errors)
        lits = []
        def collect(n):
            if n["k"] == "lit":
                lits.append(n)
            for key in ("a", "b", "c"):
                if key in n:
                    collect(n[key])
        collect(tree)
        cn = {}
        decls = ""
        for j, n in enumerate(lits):
            cn[id(n)] = f"c{j}"
            decls += f"\tvar c{j} = {GONAME[n['t']]}({signed_repr(n['t'], n['v'])})\n"
        src += (f"\n//go:noinline\nfunc v{i}(x, y uint64) (res uint64, pn string) {{\n"
                f"\tdefer func() {{ if e := recover(); e != nil {{ pn = panicName(e) }} }}()\n"
                f"{decls}"
                f"\tres = uint64({g.go(tree, cn)})\n\treturn\n}}\n")
    src += "\nfunc main() {\n\tvar r uint64\n\tvar p string\n"
    for i in range(len(trees)):
        for (x, y) in pairs:
            src += (f"\tr, p = v{i}({x}, {y})\n"
                    f"\tif p == \"\" {{\n\t\tfmt.Printf(\"e={i} x={x} y={y} OK %d\\n\", r)\n"
                    f"\t}} else {{\n\t\tfmt.Printf(\"e={i} x={x} y={y} PANIC %s\\n\", p)\n\t}}\n")
    src += "}\n"
    return recs, src


def run(seed, n, out):
    os.makedirs(out, exist_ok=True)
    gomod = os.path.join(out, "gomain")
    os.makedirs(gomod, exist_ok=True)
    recs, src = program(seed, n, 8)
    open(os.path.join(out, "exprs.json"), "w").write(json.dumps(recs))
    open(os.path.join(gomod, "main.go"), "w").write(src)
    open(os.path.join(gomod, "go.mod"), "w").write("module obits\ngo 1.25\n")
    gobin = os.environ.get("GO", "go")
    env = dict(os.environ, GOTOOLCHAIN=os.environ.get("GOTOOLCHAIN", "local"))
    gout = subprocess.run([gobin, "run", "."], cwd=gomod, capture_output=True,
                          text=True, env=env, timeout=300)
    if gout.returncode != 0:
        return f"seed {seed}: go run failed: {gout.stderr[:300]}"
    lake = os.environ.get("LAKE", "lake")
    lout = subprocess.run([lake, "exe", "oracle", os.path.abspath(os.path.join(out, "exprs.json"))],
                          capture_output=True, text=True, timeout=300)
    if lout.returncode != 0:
        return f"seed {seed}: oracle failed: {lout.stdout[:200]} {lout.stderr[:300]}"
    gl, ll = gout.stdout.splitlines(), lout.stdout.splitlines()
    diffs = [(a, b) for a, b in zip(gl, ll) if a != b]
    if len(gl) != len(ll):
        return f"seed {seed}: LINE COUNT {len(gl)} vs {len(ll)}"
    if diffs:
        return f"seed {seed}: {len(diffs)} DIFFS\n" + "\n".join(
            f"  go  : {a}\n  lean: {b}" for a, b in diffs[:5])
    return f"seed {seed}: {len(gl)} evaluations OK"


def main():
    if len(sys.argv) != 4:
        print(__doc__)
        raise SystemExit(2)
    print(run(int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]))


if __name__ == "__main__":
    main()
