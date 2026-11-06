#!/usr/bin/env python3
"""Differential campaign across Go implementations (gc, gccgo, LLGo, TinyGo, Yaegi).

Every case is a deterministic Go program derived from a seed. Each selected
toolchain builds (or interprets) it, the outputs are compared with the gc
reference, and, when the Lean oracle is given, the expression lines are also
compared with the documented semantics. gc is the *practical* reference: a
toolchain that disagrees with gc is classified, not convicted, and a gc result
that disagrees with the Lean oracle is flagged as a lead even when every other
toolchain agrees with gc (and conversely, the majority never decides).

Suites:

* ``core``     - random integer programs over the portable subset: signed and
  unsigned 8/16/32/64-bit arithmetic, bitwise operations, conversions and
  truncations, constant / variable / huge shift counts, comparisons, if/else
  selects lowered to Phi, bounded loops, ``//go:noinline`` functions. No
  ``math/bits``, no panics (division is guarded, signed counts are masked
  non-negative), Go <= 1.21 language features only.
* ``bits``     - the ``core`` generator plus ``math/bits`` calls and rotates,
  kept apart because libraries and intrinsics differ between toolchains.
* ``directed`` - the cmd/compile bugs already tracked by go-in-lean: the
  oracle_canaries.py trees (with the oracle) and the self-checking
  ``findings/*/cl/issue*.go`` regression tests (expected: exit 0).

Per (case, toolchain) status: ``clean``, ``unsupported``, ``build_error``,
``run_error``, ``timeout``, ``output_mismatch``; ``skipped`` when the gc
reference itself failed (a generator/harness problem, reported separately).
Clean case directories are removed unless ``--keep-all``; divergent ones keep
the source, the build logs, the outputs and the binaries next to report.json.

Toolchain executables come from ``--path NAME=EXE`` or the environment
(GO, GCCGO, TINYGO, YAEGI, LLGO), otherwise from PATH. Extra gc toolchains
(other releases, tip) are added with ``--extra-gc LABEL=EXE``.

Examples:

  alt_compiler_diff.py list
  alt_compiler_diff.py gen --suite core --seed 1 --index 0
  alt_compiler_diff.py run --suite core --seed 1 --count 200 --out runs/core-1 \\
      --oracle ~/oracle --jobs 16
  alt_compiler_diff.py run ... --compare-with runs/core-1/report.json
"""

from __future__ import annotations

import argparse
import concurrent.futures
import copy
from dataclasses import dataclass, field
import datetime
import hashlib
import json
import os
from pathlib import Path
import random
import re
import shlex
import shutil
import signal
import subprocess
import sys
import time

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_bits as ob  # noqa: E402  (IR helpers and RPN emission)
import oracle_canaries as oc  # noqa: E402  (directed canary trees)

HARNESS_VERSION = "1.1.0"
REPO_ROOT = Path(__file__).resolve().parent.parent
STATUSES = ("clean", "unsupported", "build_error", "run_error", "timeout",
            "output_mismatch", "skipped")
SUITES = ("core", "bits", "panics", "directed", "ext")

TYPES = ob.TYPES
GONAME = ob.GONAME
CMP_OPS = ("lt", "le", "gt", "ge", "eq", "ne")
CMP_SYM = {"lt": "<", "le": "<=", "gt": ">", "ge": ">=", "eq": "==", "ne": "!="}
BIN_SYM = {"add": "+", "sub": "-", "mul": "*", "and": "&", "or": "|",
           "xor": "^", "div": "/", "mod": "%", "andnot": "&^"}


# --------------------------------------------------------------------------
# Generator (IR shared with oracle_bits.py, so the Lean oracle can evaluate it)
# --------------------------------------------------------------------------

def lit(t, v, **flags):
    w, _ = t
    node = {"k": "lit", "t": t, "v": v % (1 << w)}
    node.update(flags)
    return node


def var(t, which):
    return {"k": "var", "t": t, "which": which}


def node_type(n):
    """Go type of an IR node; None for comparisons (bool)."""
    k = n["k"]
    if k == "bin" and n["op"] in CMP_OPS:
        return None
    if k in ("lit", "var", "conv", "sel"):
        return n["t"]
    if k in ("un",):
        return node_type(n["a"])
    if k == "bin":
        return node_type(n["a"])
    if k == "bits":
        return (64, True) if n["op"] in ("oc", "lz", "tz", "len") else (n["w"], False)
    if k == "rot":
        return (n["w"], False)
    if k in ("sub64", "add64"):
        return (64, False)
    if k == "arr":
        return (64, True)
    raise ValueError(k)


class SubsetGen:
    """Random typed trees restricted to the portable, panic-free subset."""

    def __init__(self, r: random.Random, with_bits: bool, word_bits: int = 64,
                 panics: bool = False):
        self.r = r
        self.with_bits = with_bits
        # panics suite: one unguarded division or signed count per tree, never
        # under a select (the oracle evaluates both arms, Go only the taken one)
        self.panics = panics
        self.panic_budget = 0
        self.sel_depth = 0
        # an untyped constant shift count must be representable as a uint:
        # on 32-bit targets, larger untyped counts are spelled as typed constants
        self.word_bits = word_bits

    def start_tree(self):
        self.panic_budget = 1 if self.panics else 0

    def may_panic(self, p):
        if self.panics and self.panic_budget > 0 and self.sel_depth == 0 and self.r.random() < p:
            self.panic_budget -= 1
            return True
        return False

    def leaf(self, t):
        if self.r.random() < 0.45:
            return ob.lit(self.r, t)
        return var(t, "x" if self.r.random() < 0.7 else "y")

    def count(self, w, d):
        """A shift count that can never be negative."""
        r = self.r
        if self.may_panic(0.3):
            # signed count, not masked: negative when y's low bits say so
            cw = r.choice((8, 16, 32, 64))
            return {"k": "conv", "t": (cw, True), "a": var((64, False), "y"),
                    "panic_site": True}
        k = r.random()
        if k < 0.45:
            c = r.choice(ob.COUNTS + [w - 1, w, w + 1, 2 * w + 1])
            return lit((64, False), c)
        if k < 0.65:
            return var((64, False), "y")
        if k < 0.80:
            cw = r.choice((8, 16, 32, 64))
            return {"k": "conv", "t": (cw, False), "a": var((64, False), "y")}
        if k < 0.92:
            # signed count, masked to a non-negative (possibly huge) value
            cw = r.choice((8, 16, 32, 64))
            return {"k": "bin", "op": "and",
                    "a": {"k": "conv", "t": (cw, True), "a": var((64, False), "y")},
                    "b": lit((cw, True), (1 << (cw - 1)) - 1)}
        return self.build((64, False), d - 1)

    def nonzero(self, b, t):
        """Guard a divisor: literal zero becomes 3, others select 1 on zero."""
        if b["k"] == "lit":
            if b["v"] == 0:
                b["v"] = 3
            return b
        # "guard": the condition evaluates a copy of b first, so a panic inside
        # b happens in the condition, identically in Go and in the oracle
        return {"k": "sel", "t": t, "guard": True,
                "c": {"k": "bin", "op": "eq", "a": copy.deepcopy(b), "b": lit(t, 0)},
                "a": lit(t, 1), "b": b}

    def cmp(self, d):
        t = self.r.choice(TYPES)
        return {"k": "bin", "op": self.r.choice(CMP_OPS),
                "a": self.build(t, d), "b": self.build(t, d)}

    def build(self, t, d):
        r = self.r
        if d <= 0 or r.random() < 0.25:
            return self.leaf(t)
        w, s = t
        k = r.random()
        if k < 0.32:
            op = r.choice(["add", "sub", "mul", "and", "or", "xor", "andnot"])
            return {"k": "bin", "op": op, "a": self.build(t, d - 1), "b": self.build(t, d - 1)}
        if k < 0.42:
            op = r.choice(["div", "mod"])
            a = self.build(t, d - 1)
            b = self.build(t, d - 1)
            if self.may_panic(0.6):
                return {"k": "bin", "op": op, "a": a, "b": b, "panic_site": True}
            return {"k": "bin", "op": op, "a": a, "b": self.nonzero(b, t)}
        if k < 0.58:
            return {"k": "bin", "op": r.choice(["shl", "shr"]),
                    "a": self.build(t, d - 1), "b": self.count(w, d)}
        if k < 0.66:
            return {"k": "un", "op": r.choice(["neg", "com"]), "a": self.build(t, d - 1)}
        if k < 0.78:
            src = r.choice(TYPES)
            if r.random() < 0.15:
                # bool -> integer, through b2i
                return {"k": "conv", "t": t, "a": self.cmp(d - 1)}
            return {"k": "conv", "t": t, "a": self.build(src, d - 1)}
        if k < 0.90:
            self.sel_depth += 1
            c = self.cmp(d - 1)
            a = self.build(t, d - 1)
            b = self.build(t, d - 1)
            self.sel_depth -= 1
            return {"k": "sel", "t": t, "c": c, "a": a, "b": b}
        if self.with_bits:
            if t == (64, True):
                iw = r.choice([8, 16, 32, 64])
                return {"k": "bits", "op": r.choice(["oc", "lz", "tz", "len"]), "w": iw,
                        "a": self.build((iw, False), d - 1)}
            if not s:
                if r.random() < 0.5:
                    kk = r.choice([0, 1, 2, 3, 7, w - 1, w, -1, -3, -w])
                    return {"k": "rot", "w": w, "a": self.build(t, d - 1),
                            "c": lit((64, True), kk)}
                op = "rb" if (w >= 16 and r.random() < 0.5) else "rev"
                return {"k": "bits", "op": op, "w": w, "a": self.build(t, d - 1)}
        return {"k": "bin", "op": r.choice(["add", "xor", "sub"]),
                "a": self.build(t, d - 1), "b": self.build(t, d - 1)}

    def assign_literal_modes(self, n, parent=None, slot=None):
        """Choose how each literal is spelled: a local variable (default), a
        typed constant, or an untyped constant. A binary operator never gets
        two constant operands (constant -x, x/0 or overflowing constant
        arithmetic would be compile errors), and literals below unary
        operators, conversions, intrinsics or at the top stay variables."""
        k = n["k"]
        if k == "bin":
            a, b = n["a"], n["b"]
            lits = [c for c in ("a", "b") if n[c]["k"] == "lit"]
            if lits:
                pick = self.r.choice(lits)
                mode = self.r.choices(["var", "raw", "untyped"], [0.5, 0.3, 0.2])[0]
                if mode == "untyped" and n["op"] in ("shl", "shr") and pick == "a":
                    mode = "raw"
                if (mode == "untyped" and n["op"] in ("shl", "shr") and pick == "b"
                        and n["b"]["v"] >= 1 << self.word_bits):
                    mode = "raw"  # no extra random draw: other programs are unchanged
                if n.get("panic_site") and pick == "b":
                    mode = "var"  # a constant zero divisor is a compile error
                if mode != "var":
                    n[pick][mode] = True
            for c in (a, b):
                if c["k"] != "lit":
                    self.assign_literal_modes(c, n)
            return
        if k == "sel":
            self.assign_literal_modes(n["c"], n)
            for c in ("a", "b"):
                ch = n[c]
                if ch["k"] == "lit":
                    mode = self.r.choices(["var", "raw", "untyped"], [0.5, 0.3, 0.2])[0]
                    if mode != "var":
                        ch[mode] = True
                else:
                    self.assign_literal_modes(ch, n)
            return
        for c in ("a", "b", "c"):
            if c in n and n[c]["k"] != "lit":
                self.assign_literal_modes(n[c], n)


class ExtGen(SubsetGen):
    """The ext suite: shapes aimed at extension elision in the lowering.

    Identity detours (f ^ f, f - f) that generic optimization folds away but
    that reach the lowered rules intact in -N builds (no CSE), where they
    become `& -1`, `| 0` or `+ 0` next to a zero or sign extension
    (golang/go#36897); nested conversions of mixed width and signedness; and
    narrow(wide(e) >> c), the shape of golang/go#82775. Everything stays in
    the node kinds of the other suites, so the oracle and the emitter are
    unchanged.
    """

    def __init__(self, r: random.Random, with_bits: bool = True, word_bits: int = 64):
        super().__init__(r, with_bits=with_bits, word_bits=word_bits)

    def zero(self, t, d):
        """An expression that is always 0: f ^ f or f - f on a copy of f."""
        f = super().build(t, max(d - 1, 0))
        return {"k": "bin", "op": self.r.choice(["xor", "sub"]), "a": f, "b": copy.deepcopy(f)}

    def build(self, t, d):
        r = self.r
        if d <= 0 or r.random() < 0.6:
            return super().build(t, d)
        w, s = t
        k = r.random()
        if k < 0.3:  # e &^ 0, e & ^0: an ANDconst [-1] after lowering
            e = self.build(t, d - 1)
            z = self.zero(t, d - 1)
            if r.random() < 0.5:
                return {"k": "bin", "op": "andnot", "a": e, "b": z}
            return {"k": "bin", "op": "and", "a": e, "b": {"k": "un", "op": "com", "a": z}}
        if k < 0.45:  # e | 0, e + 0, e - 0, e ^ 0
            return {"k": "bin", "op": r.choice(["or", "add", "sub", "xor"]),
                    "a": self.build(t, d - 1), "b": self.zero(t, d - 1)}
        if k < 0.75:  # nested conversions
            m1, m2 = r.choice(TYPES), r.choice(TYPES)
            inner = {"k": "conv", "t": m2, "a": self.build(r.choice(TYPES), d - 1)}
            return {"k": "conv", "t": t, "a": {"k": "conv", "t": m1, "a": inner}}
        # narrow(wide(e) >> c), with the result converted back to t
        wide = r.choice([(32, True), (32, False), (64, True), (64, False)])
        narrow = r.choice([(8, True), (8, False), (16, True), (16, False)])
        c = lit((64, False), r.choice([1, 3, 7, 8, 15, 16, 17, 24, 31]))
        sh = {"k": "bin", "op": "shr", "a": {"k": "conv", "t": wide, "a": self.build(r.choice(TYPES), d - 1)},
              "b": c}
        return {"k": "conv", "t": t, "a": {"k": "conv", "t": narrow, "a": sh}}


# --------------------------------------------------------------------------
# Go emission: statements for selects (real Phi), optional SSA-style temps
# --------------------------------------------------------------------------

class Emitter:
    def __init__(self, r: random.Random | None, bind_prob=0.0, sel_style="mixed",
                 names=None):
        self.r = r
        self.bind_prob = bind_prob
        self.sel_style = sel_style
        self.names = names or {"x": "x", "y": "y"}
        self.lines: list[str] = []
        self.decls: list[str] = []
        self.indent = 1
        self.tmp = 0
        self.uses_bits = False
        self.lit_names: dict[int, str] = {}

    def emit(self, s):
        self.lines.append("\t" * self.indent + s)

    def fresh(self):
        self.tmp += 1
        return f"t{self.tmp}"

    def lit_ref(self, n):
        t = GONAME[n["t"]]
        v = ob.signed_repr(n["t"], n["v"])
        if n.get("untyped"):
            return f"({v})" if v < 0 else str(v)
        if n.get("raw"):
            return f"{t}({v})"
        key = id(n)
        if key not in self.lit_names:
            name = f"c{len(self.lit_names)}"
            self.lit_names[key] = name
            self.decls.append(f"\tvar {name} = {t}({v})")
        return self.lit_names[key]

    def maybe_bind(self, expr):
        if self.r is not None and self.bind_prob and self.r.random() < self.bind_prob:
            name = self.fresh()
            self.emit(f"{name} := {expr}")
            return name
        return expr

    def expr(self, n):
        k = n["k"]
        if k == "lit":
            return self.lit_ref(n)
        if k == "var":
            return f"{GONAME[n['t']]}({self.names[n['which']]})"
        if k == "un":
            a = self.expr(n["a"])
            return self.maybe_bind(f"(-{a})" if n["op"] == "neg" else f"(^{a})")
        if k == "bin":
            a = self.expr(n["a"])
            b = self.expr(n["b"])
            op = n["op"]
            if op in ("shl", "shr"):
                out = f"({a} {'<<' if op == 'shl' else '>>'} {b})"
            elif op in ("min", "max"):
                out = f"{op}({a}, {b})"
            elif op in CMP_OPS:
                return f"({a} {CMP_SYM[op]} {b})"
            else:
                out = f"({a} {BIN_SYM[op]} {b})"
            return self.maybe_bind(out)
        if k == "conv":
            inner = self.expr(n["a"])
            if node_type(n["a"]) is None:
                return self.maybe_bind(f"{GONAME[n['t']]}(b2i({inner}))")
            return self.maybe_bind(f"{GONAME[n['t']]}({inner})")
        if k == "bits":
            self.uses_bits = True
            fn = {"oc": "OnesCount", "lz": "LeadingZeros", "tz": "TrailingZeros",
                  "len": "Len", "rev": "Reverse", "rb": "ReverseBytes"}[n["op"]] + str(n["w"])
            a = self.expr(n["a"])
            if n["op"] in ("oc", "lz", "tz", "len"):
                return self.maybe_bind(f"int64(bits.{fn}({a}))")
            return self.maybe_bind(f"bits.{fn}({a})")
        if k == "rot":
            self.uses_bits = True
            a = self.expr(n["a"])
            c = self.expr(n["c"])
            return self.maybe_bind(f"bits.RotateLeft{n['w']}({a}, int({c}))")
        if k in ("sub64", "add64"):
            self.uses_bits = True
            fn = "Sub64" if k == "sub64" else "Add64"
            a, b, c = self.expr(n["a"]), self.expr(n["b"]), self.expr(n["c"])
            first, second = ("d0", "_") if n["o"] in ("diff", "sum") else ("_", "d1")
            idx = 0 if first == "d0" else 1
            return (f"(func() uint64 {{ {first}, {second} := bits.{fn}({a}, {b}, {c}); "
                    f"return d{idx} }}())")
        if k == "arr":
            return f"ga[{self.expr(n['i'])}]"
        if k == "sel":
            return self.sel(n)
        raise ValueError(k)

    def sel(self, n):
        style = self.sel_style
        if style == "mixed":
            style = self.r.choice(("ifelse", "default")) if self.r else "ifelse"
        name = self.fresh()
        t = GONAME[n["t"]]
        cond = self.expr(n["c"])
        if style == "default":
            # r = <else>; if <c> { r = <then> }   (the oracle_canaries shape)
            self.emit(f"var {name} {t}")
            self.emit(f"{name} = {self.expr(n['b'])}")
            self.emit(f"if {cond} {{")
            self.indent += 1
            self.emit(f"{name} = {self.expr(n['a'])}")
            self.indent -= 1
            self.emit("}")
        else:
            self.emit(f"var {name} {t}")
            self.emit(f"if {cond} {{")
            self.indent += 1
            self.emit(f"{name} = {self.expr(n['a'])}")
            self.indent -= 1
            self.emit("} else {")
            self.indent += 1
            self.emit(f"{name} = {self.expr(n['b'])}")
            self.indent -= 1
            self.emit("}")
        return name


def result_expr(n, e: Emitter):
    body = e.expr(n)
    if node_type(n) is None:
        return f"b2i({body})"
    return f"uint64({body})"


PANIC_HELPERS = '''
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
'''

GO_HELPERS = '''
var ga = [8]int64{1, 2, 3, 7, 15, 255, -1, -128}

var _ = ga

func b2i(b bool) uint64 {
	if b {
		return 1
	}
	return 0
}
'''


@dataclass
class Program:
    source: str
    records: list  # RPN records for the Lean oracle (e= lines only)
    meta: dict = field(default_factory=dict)
    trees: list = field(default_factory=list)  # IR of the oracle-checked functions


def emit_program(funcs, loops, pairs, input_mode, rng, bind_prob, sel_style, panics=False,
                 func_pairs=None):
    """funcs: IR trees (oracle-checked); loops: (tree, type) pairs (gc-checked).
    With panics, each function recovers and reports the panic kind as the
    oracle does (`... PANIC divideError`). func_pairs: optional inputs per
    function (SMT-guided); loops always use pairs."""
    fpairs = func_pairs if func_pairs is not None else [pairs] * len(funcs)
    chunks = []
    uses_bits = False
    g = ob.Gen(None)
    records = []
    for i, tree in enumerate(funcs):
        e = Emitter(rng, bind_prob, sel_style)
        res = result_expr(tree, e)
        uses_bits |= e.uses_bits
        body = "".join(line + "\n" for line in e.decls + e.lines)
        if panics:
            chunks.append(f"//go:noinline\nfunc v{i}(x, y uint64) (res uint64, pn string) {{\n"
                          "\tdefer func() {\n\t\tif e := recover(); e != nil {\n"
                          "\t\t\tpn = panicName(e)\n\t\t}\n\t}()\n"
                          f"{body}\tres = {res}\n\treturn\n}}\n")
        else:
            chunks.append(f"//go:noinline\nfunc v{i}(x, y uint64) uint64 {{\n"
                          f"{body}\treturn {res}\n}}\n")
        for (x, y) in fpairs[i]:
            ops = []
            g.rpn(tree, x, y, ops)
            records.append({"e": i, "x": x, "y": y, "ops": ops})
    for i, (tree, t) in enumerate(loops):
        e = Emitter(rng, bind_prob, sel_style, names={"x": "xx", "y": "y"})
        e.indent = 2
        inner = e.expr(tree)
        uses_bits |= e.uses_bits
        tn = GONAME[t]
        chunks.append(
            f"//go:noinline\nfunc l{i}(x, y uint64) uint64 {{\n"
            + "\n".join(e.decls) + ("\n" if e.decls else "")
            + f"\tvar acc {tn}\n\tn := 2 + (y & 3)\n"
            f"\tfor j := uint64(0); j < n; j++ {{\n"
            f"\t\txx := x + j*0x9E3779B97F4A7C15\n\t\t_ = xx\n"
            + "\n".join(e.lines) + ("\n" if e.lines else "")
            + f"\t\tacc = acc*3 ^ {inner}\n\t}}\n\treturn uint64(acc)\n}}\n")
    pkgs = ["fmt"] + (["math/bits"] if uses_bits else []) + (["strings"] if panics else [])
    imports = ("import (\n" + "".join(f'\t"{p}"\n' for p in pkgs) + ")\n"
               if len(pkgs) > 1 else 'import "fmt"\n')
    main = ["func main() {"]
    if panics:
        main += ["\tvar r uint64", "\tvar p string"]
    if input_mode == "runtime":
        # inputs filled at run time: a literal argument could be propagated
        # into the noinline callee by an interprocedural optimizer
        allp = list(pairs)
        if func_pairs is not None:
            for fp in func_pairs:
                allp += [p for p in fp if p not in allp]
        index = {p: j for j, p in reversed(list(enumerate(allp)))}
        flat = ", ".join(str(v) for p in allp for v in p)
        chunks.append(f"var gin = [{2 * len(allp)}]uint64{{{flat}}}\n")
        main += [f"\tvar in [{len(allp)}][2]uint64",
                 f"\tfor i := 0; i < {2 * len(allp)}; i += 2 {{",
                 "\t\tin[i/2][0] = gin[i]", "\t\tin[i/2][1] = gin[i+1]", "\t}"]
        arg = lambda j, x, y: f"in[{index[(x, y)]}][0], in[{index[(x, y)]}][1]"  # noqa: E731
    else:
        arg = lambda j, x, y: f"{x}, {y}"  # noqa: E731
    for i in range(len(funcs)):
        for j, (x, y) in enumerate(fpairs[i]):
            if panics:
                main += [f"\tr, p = v{i}({arg(j, x, y)})",
                         f'\tif p == "" {{\n\t\tfmt.Printf("e={i} x={x} y={y} OK %d\\n", r)\n'
                         f'\t}} else {{\n\t\tfmt.Printf("e={i} x={x} y={y} PANIC %s\\n", p)\n\t}}']
            else:
                main.append(f'\tfmt.Printf("e={i} x={x} y={y} OK %d\\n", v{i}({arg(j, x, y)}))')
    for i in range(len(loops)):
        for j, (x, y) in enumerate(pairs):
            main.append(f'\tfmt.Printf("l={i} x={x} y={y} OK %d\\n", l{i}({arg(j, x, y)}))')
    main.append("}")
    src = ("package main\n\n" + imports + (PANIC_HELPERS if panics else "") + GO_HELPERS + "\n"
           + "\n".join(chunks) + "\n" + "\n".join(main) + "\n")
    return src, records


def random_program(suite, seed, index, nfuncs=10, nloops=2, npairs=6, depth=3,
                   word_bits=64, inputs="pool"):
    """inputs: "pool" draws npairs (x, y) from oracle_bits.XPOOL, shared by all
    functions; "smt" gives each function npairs inputs chosen by z3 on its
    semantic boundaries (smt_inputs.py), completed from the pool; "mixed"
    takes half of them from z3 and half from the pool (the two selections
    find different bugs). The trees and the loop inputs are the same in
    every mode."""
    rng = random.Random(f"{suite}:{seed}:{index}")
    panics = suite == "panics"
    if panics:
        nloops = 0  # loop bodies are not checked by the oracle
    if suite == "ext":
        gen = ExtGen(rng, word_bits=word_bits)
    else:
        gen = SubsetGen(rng, with_bits=(suite == "bits"), word_bits=word_bits, panics=panics)
    funcs = []
    for _ in range(nfuncs):
        gen.start_tree()
        if rng.random() < 0.15:
            tree = gen.cmp(rng.randint(1, 2))
        else:
            tree = gen.build(rng.choice(TYPES), rng.randint(1, depth))
        gen.assign_literal_modes(tree)
        funcs.append(tree)
    loops = []
    for _ in range(nloops):
        t = rng.choice(TYPES)
        tree = gen.build(t, rng.randint(1, depth))
        gen.assign_literal_modes(tree)
        loops.append((tree, t))
    pairs = [(rng.choice(ob.XPOOL), rng.choice(ob.XPOOL)) for _ in range(npairs)]
    input_mode = rng.choice(("literal", "runtime"))
    bind_prob = rng.choice((0.0, 0.4))
    func_pairs = None
    meta = {"input_mode": input_mode, "bind_prob": bind_prob,
            "funcs": nfuncs, "loops": nloops, "pairs": npairs}
    if inputs in ("smt", "mixed"):
        import smt_inputs  # needs z3; imported only in this mode
        func_pairs, meta["smt_targets"] = [], []
        for i, tree in enumerate(funcs):
            srng = random.Random(f"smt:{suite}:{seed}:{index}:{i}")
            k = npairs if inputs == "smt" else npairs // 2
            got, labels = smt_inputs.smt_pairs(tree, k, srng)
            func_pairs.append(smt_inputs.fill(got, npairs, ob.XPOOL, srng))
            meta["smt_targets"].append(labels)
        meta["inputs"] = inputs
    elif inputs != "pool":
        raise ValueError(f"unknown input selection {inputs!r}")
    src, records = emit_program(funcs, loops, pairs, input_mode, rng, bind_prob, "mixed",
                                panics=panics, func_pairs=func_pairs)
    return Program(src, records, meta, trees=funcs)


# --------------------------------------------------------------------------
# Directed suite
# --------------------------------------------------------------------------

ICE_82767 = '''package main

import "fmt"

//go:noinline
func F(y int32) int32 {
	return (y >> 1) >> (uint32(1) << 31)
}

func main() { fmt.Println(F(2), F(-5)) }
'''

SPILL_80577 = REPO_ROOT / "findings" / "PPC64-SPILL-SIGNEXT-80577" / "minimal_reproducer.go"


def directed_cases():
    """Return (name, Program, expectation) tuples. expectation is "reference"
    (compare with gc and the oracle) or "selfcheck" (exit 0 is correct)."""
    cases = []
    for c in oc.CANARIES:
        tree = copy.deepcopy(c["tree"])
        src, records = emit_program([tree], [], c["inputs"], "runtime", None, 0.0, "default")
        meta = {"canary": c["id"], "expect": list(c["expect"]),
                "host_relevant": "arch" not in c}
        cases.append((f"canary-{c['id']}", Program(src, records, meta), "reference"))
    for path in sorted(REPO_ROOT.glob("findings/*/cl/issue*.go")):
        text = path.read_text()
        if re.search(r'"(simd|unsafe|reflect)"|GOEXPERIMENT|^//go:build', text, re.M):
            continue
        cases.append((f"cl-{path.stem}", Program(text, [], {"file": str(path.relative_to(REPO_ROOT))}),
                      "selfcheck"))
    cases.append(("ice-82767-main", Program(ICE_82767, [], {"issue": "82767"}), "reference"))
    if SPILL_80577.exists():
        cases.append(("spill-80577", Program(SPILL_80577.read_text(), [],
                                             {"issue": "80577", "want": "-1001"}), "reference"))
    return cases


# --------------------------------------------------------------------------
# Toolchain adapters
# --------------------------------------------------------------------------

@dataclass
class Adapter:
    name: str
    family: str           # gc | gccgo | tinygo | llgo | yaegi
    env_var: str
    default_exe: str
    build_flags: tuple = ()
    interpreted: bool = False
    version_args: tuple = ("version",)
    extra_env: dict = field(default_factory=dict)
    # build diagnostics that mean "feature not implemented by this toolchain"
    unsupported: tuple = ()
    # cross-target runs: a command prepended to compiled binaries (qemu-user)
    # and flags appended to the build (e.g. -static for a cross gccgo)
    run_prefix: tuple = ()
    extra_flags: tuple = ()
    exe: str | None = None
    version: str | None = None
    available: bool = False
    reason: str = ""

    def build_argv(self, src: str, out: str):
        flags = (*self.build_flags, *self.extra_flags)
        if self.family == "gc":
            return [self.exe, "build", *flags, "-o", out, src]
        if self.family == "gccgo":
            return [self.exe, *flags, "-o", out, src]
        if self.family in ("tinygo", "llgo"):
            return [self.exe, "build", *flags, "-o", out, src]
        raise ValueError(self.family)

    def run_argv(self, src: str, binary: str):
        if self.interpreted:
            return [self.exe, "run", src]
        return [*self.run_prefix, binary]

    def describe(self):
        return {"family": self.family, "exe": self.exe, "available": self.available,
                "version": self.version, "reason": self.reason,
                "build": None if self.interpreted else
                shlex.join(self.build_argv("main.go", "prog")),
                "run": shlex.join(self.run_argv("main.go", "./prog")),
                "extra_flags": list(self.extra_flags),
                "env": self.extra_env}


GC_ENV = {"GO111MODULE": "off", "GOTOOLCHAIN": "local", "CGO_ENABLED": "0", "GOFLAGS": ""}
UNSUPPORTED_COMMON = (r"not (yet )?implemented", r"unsupported", r"not supported")


def default_adapters():
    return [
        Adapter("gc", "gc", "GO", "go", extra_env=dict(GC_ENV)),
        Adapter("gc-noopt", "gc", "GO", "go", build_flags=("-gcflags=all=-N -l",),
                extra_env=dict(GC_ENV)),
        Adapter("gccgo-O0", "gccgo", "GCCGO", "gccgo", build_flags=("-O0",),
                version_args=("--version",), unsupported=UNSUPPORTED_COMMON),
        Adapter("gccgo-O2", "gccgo", "GCCGO", "gccgo", build_flags=("-O2",),
                version_args=("--version",), unsupported=UNSUPPORTED_COMMON),
        Adapter("tinygo", "tinygo", "TINYGO", "tinygo", unsupported=UNSUPPORTED_COMMON),
        Adapter("llgo", "llgo", "LLGO", "llgo", unsupported=UNSUPPORTED_COMMON),
        Adapter("yaegi", "yaegi", "YAEGI", "yaegi", interpreted=True,
                unsupported=UNSUPPORTED_COMMON),
    ]


def apply_cross_options(adapters, prefixes, extra):
    """Set run prefixes and extra build flags from NAME=VALUE maps, where NAME
    is an adapter name or a family; the adapter name wins over its family."""
    for a in adapters:
        p = prefixes.get(a.name, prefixes.get(a.family))
        if p is not None and not a.interpreted:
            a.run_prefix = tuple(shlex.split(os.path.expanduser(p)))
        f = extra.get(a.name, extra.get(a.family))
        if f is not None:
            a.extra_flags = tuple(shlex.split(f))
    return adapters


def resolve_exe(candidate):
    if not candidate:
        return None
    if os.sep in candidate:
        p = Path(candidate).expanduser()
        # absolute, but symlinks kept: wrappers such as /snap/bin/go dispatch on argv[0]
        return os.path.abspath(p) if p.is_file() and os.access(p, os.X_OK) else None
    return shutil.which(candidate)


def git_head(path: Path):
    """Commit of a checkout, read without invoking git."""
    head = path / ".git" / "HEAD"
    try:
        ref = head.read_text().strip()
    except OSError:
        return None
    if not ref.startswith("ref: "):
        return ref
    name = ref[5:]
    loose = path / ".git" / name
    if loose.exists():
        return loose.read_text().strip()
    packed = path / ".git" / "packed-refs"
    if packed.exists():
        for line in packed.read_text().splitlines():
            if line.endswith(" " + name):
                return line.split()[0]
    return None


def detect(adapters, paths, tool_env, timeout=120):
    for a in adapters:
        cand = paths.get(a.name) or paths.get(a.family) or os.environ.get(a.env_var) \
            or a.default_exe
        a.exe = resolve_exe(cand)
        for k, v in tool_env.get(a.name, {}).items():
            a.extra_env[k] = v
        for k, v in tool_env.get(a.family, {}).items():
            a.extra_env.setdefault(k, v)
        if not a.exe:
            a.available, a.reason = False, f"executable not found: {cand}"
            continue
        env = dict(os.environ, **a.extra_env)
        try:
            p = subprocess.run([a.exe, *a.version_args], capture_output=True, text=True,
                               timeout=timeout, env=env)
        except (OSError, subprocess.TimeoutExpired) as exc:
            a.available, a.reason = False, f"version probe failed: {exc}"
            continue
        text = (p.stdout + p.stderr).strip()
        a.version = text.splitlines()[0] if text else ""
        if a.family == "llgo":
            root = a.extra_env.get("LLGO_ROOT") or os.environ.get("LLGO_ROOT")
            commit = git_head(Path(root)) if root else None
            if commit:
                a.version += f" (commit {commit})"
        a.available = p.returncode == 0
        if not a.available:
            a.reason = f"version probe exit {p.returncode}: {text[:200]}"
    return adapters


# --------------------------------------------------------------------------
# Execution
# --------------------------------------------------------------------------

def run_cmd(argv, cwd, env, timeout):
    t0 = time.monotonic()
    proc = subprocess.Popen(argv, cwd=cwd, env=env, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
        timed_out = False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        timed_out = True
    return {"argv": argv, "rc": proc.returncode, "stdout": out, "stderr": err,
            "seconds": round(time.monotonic() - t0, 3), "timed_out": timed_out}


def tail(text, n=2000):
    return text if len(text) <= n else "..." + text[-n:]


def first_diffs(a, b, limit=5):
    al, bl = a.splitlines(), b.splitlines()
    out = []
    for i in range(max(len(al), len(bl))):
        x = al[i] if i < len(al) else "<missing>"
        y = bl[i] if i < len(bl) else "<missing>"
        if x != y:
            out.append({"line": i + 1, "reference": x, "got": y})
            if len(out) >= limit:
                break
    return out


def execute(adapter, case_dir: Path, args):
    env = dict(os.environ, **adapter.extra_env)
    src = "main.go"
    tdir = case_dir / adapter.name
    tdir.mkdir(exist_ok=True)
    binary = str(tdir / "prog")
    res = {"status": None}
    if not adapter.interpreted:
        b = run_cmd(adapter.build_argv(src, binary), case_dir, env, args.build_timeout)
        (tdir / "build.log").write_text(b["stdout"] + b["stderr"])
        res["build"] = {"argv": shlex.join(b["argv"]), "rc": b["rc"], "seconds": b["seconds"]}
        if b["timed_out"]:
            res.update(status="timeout", phase="build")
            return res
        if b["rc"] != 0:
            diag = b["stdout"] + b["stderr"]
            res["diagnostic"] = tail(diag)
            pats = adapter.unsupported
            if pats and any(re.search(p, diag, re.I) for p in pats):
                res["status"] = "unsupported"
            else:
                res["status"] = "build_error"
            return res
    r = run_cmd(adapter.run_argv(src, binary), case_dir, env, args.run_timeout)
    (tdir / "stdout.txt").write_text(r["stdout"])
    (tdir / "stderr.txt").write_text(r["stderr"])
    res["run"] = {"argv": shlex.join(r["argv"]), "rc": r["rc"], "seconds": r["seconds"]}
    res["stdout"], res["stderr"], res["rc"] = r["stdout"], r["stderr"], r["rc"]
    if r["timed_out"]:
        res.update(status="timeout", phase="run")
    return res


def oracle_eval(records, case_dir: Path, oracle, timeout):
    if not oracle or not records:
        return None
    path = case_dir / "exprs.json"
    path.write_text(json.dumps(records))
    r = run_cmd([oracle, str(path.resolve())], case_dir, dict(os.environ), timeout)
    if r["rc"] != 0 or r["timed_out"]:
        return {"error": tail(r["stdout"] + r["stderr"], 500)}
    (case_dir / "oracle.txt").write_text(r["stdout"])
    return {"lines": r["stdout"].splitlines()}


def oracle_verdict(stdout, oracle_lines):
    if oracle_lines is None:
        return "n/a"
    got = [l for l in stdout.splitlines() if l.startswith("e=")]
    return "agree" if got == oracle_lines else "disagree"


def classify(res, ref, mode):
    """Status of one toolchain result against the reference result."""
    if res["status"]:
        return res["status"]
    if mode == "selfcheck":
        if res["rc"] != 0:
            return "run_error"
        return "clean"
    if res["rc"] != ref["rc"]:
        return "run_error" if res["rc"] != 0 else "output_mismatch"
    if res["stdout"] != ref["stdout"] or res["stderr"] != ref["stderr"]:
        return "output_mismatch"
    return "clean"


def run_case(name, prog: Program, mode, adapters, args):
    case_dir = args.out / name
    if case_dir.exists():
        shutil.rmtree(case_dir)
    case_dir.mkdir(parents=True)
    (case_dir / "main.go").write_text(prog.source)
    sha = hashlib.sha256(prog.source.encode()).hexdigest()
    oracle = oracle_eval(prog.records, case_dir, args.oracle, args.run_timeout)
    oracle_lines = oracle.get("lines") if oracle else None
    results = {a.name: execute(a, case_dir, args) for a in adapters}
    ref = results[args.reference]
    ref_ok = ref["status"] is None and (ref["rc"] == 0 or mode == "selfcheck")
    record = {"name": name, "mode": mode, "sha256": sha, "meta": prog.meta,
              "toolchains": {}}
    if oracle and "error" in oracle:
        record["oracle_error"] = oracle["error"]
    for a in adapters:
        res = results[a.name]
        if mode == "reference" and not ref_ok and a.name != args.reference:
            status = "skipped"
        elif a.name == args.reference and mode == "reference":
            status = res["status"] or ("clean" if res["rc"] == 0 else "run_error")
        else:
            status = classify(res, ref, mode)
        entry = {"status": status}
        for k in ("build", "run", "phase", "diagnostic", "rc"):
            if k in res:
                entry[k] = res[k]
        if "stdout" in res:
            entry["stdout_sha256"] = hashlib.sha256(res["stdout"].encode()).hexdigest()
            if res["stderr"]:
                entry["stderr"] = tail(res["stderr"], 1000)
            entry["oracle"] = oracle_verdict(res["stdout"], oracle_lines)
            if status == "output_mismatch":
                entry["diffs"] = first_diffs(ref["stdout"], res["stdout"])
            if entry["oracle"] == "disagree" and oracle_lines is not None:
                got = [l for l in res["stdout"].splitlines() if l.startswith("e=")]
                entry["oracle_diffs"] = first_diffs("\n".join(oracle_lines), "\n".join(got))
        record["toolchains"][a.name] = entry
    record["reference_ok"] = ref_ok
    record["leads"] = leads(record, args.reference)
    interesting = (not ref_ok) or record["leads"] or any(
        e["status"] != "clean" for e in record["toolchains"].values())
    record["interesting"] = bool(interesting)
    if not interesting and not args.keep_all:
        shutil.rmtree(case_dir)
    else:
        (case_dir / "case.json").write_text(json.dumps(record, indent=2) + "\n")
    return record


def leads(record, reference):
    """Hints for triage; never a verdict."""
    out = []
    tcs = record["toolchains"]
    ref = tcs.get(reference, {})
    if ref.get("oracle") == "disagree":
        agreeing = [n for n, e in tcs.items() if e.get("oracle") == "agree"]
        out.append({"kind": "gc_vs_oracle", "reference": reference,
                    "toolchains_agreeing_with_oracle": agreeing})
    if record["mode"] == "selfcheck" and ref.get("status") != "clean":
        out.append({"kind": "gc_selfcheck_failed", "reference": reference})
    for n, e in tcs.items():
        if n != reference and e["status"] == "output_mismatch":
            r, t = ref.get("oracle"), e.get("oracle")
            if r == "agree" and t == "disagree":
                suspect = n
            elif r == "disagree" and t == "agree":
                suspect = reference
            else:
                suspect = "unknown"  # e.g. only loop (l=) lines differ
            out.append({"kind": "mismatch", "toolchain": n, "suspect": suspect})
    return out


def cmd_run(args):
    args.out = Path(args.out).expanduser().resolve()
    args.out.mkdir(parents=True, exist_ok=True)
    if args.oracle:
        args.oracle = resolve_exe(args.oracle)
        if not args.oracle:
            raise SystemExit("--oracle: not an executable")
    adapters = select_adapters(args)
    if args.reference not in {a.name for a in adapters}:
        raise SystemExit(f"reference toolchain {args.reference!r} is not available/selected")
    if args.suite == "directed":
        cases = directed_cases()
    else:
        cases = [(f"{args.suite}-{args.seed}-{i:05d}",
                  random_program(args.suite, args.seed, i, args.funcs, args.loops,
                                 args.pairs, args.depth, args.word_bits, args.inputs), "reference")
                 for i in range(args.start, args.start + args.count)]
    t0 = time.monotonic()
    started = datetime.datetime.now(datetime.timezone.utc).isoformat(timespec="seconds")
    records = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        futs = [pool.submit(run_case, n, p, m, adapters, args) for n, p, m in cases]
        for k, f in enumerate(concurrent.futures.as_completed(futs), 1):
            records.append(f.result())
            if args.progress and k % args.progress == 0:
                print(f"  {k}/{len(cases)} cases", file=sys.stderr, flush=True)
    records.sort(key=lambda r: r["name"])
    summary = {a.name: {s: 0 for s in STATUSES} for a in adapters}
    oracle_summary = {a.name: {"agree": 0, "disagree": 0, "n/a": 0} for a in adapters}
    for r in records:
        for n, e in r["toolchains"].items():
            summary[n][e["status"]] += 1
            if "oracle" in e:
                oracle_summary[n][e["oracle"]] += 1
    report = {
        "harness": {"script": "scripts/alt_compiler_diff.py", "version": HARNESS_VERSION,
                    "argv": sys.argv, "python": sys.version.split()[0]},
        "started": started,
        "seconds": round(time.monotonic() - t0, 1),
        "suite": args.suite, "seed": args.seed, "start": args.start,
        "target": args.target,
        "count": len(cases), "reference": args.reference,
        "generator": {"funcs": args.funcs, "loops": args.loops, "pairs": args.pairs,
                      "depth": args.depth, "word_bits": args.word_bits,
                      "inputs": args.inputs},
        "timeouts": {"build": args.build_timeout, "run": args.run_timeout},
        "jobs": args.jobs,
        "oracle": args.oracle,
        "toolchains": {a.name: a.describe() for a in adapters},
        "summary": summary,
        "oracle_summary": oracle_summary if args.oracle else None,
        "reference_failures": [r["name"] for r in records if not r["reference_ok"]],
        "leads": [{"case": r["name"], **l} for r in records for l in r["leads"]],
        "case_index": [{"name": r["name"], "sha256": r["sha256"],
                        "statuses": {n: e["status"] for n, e in r["toolchains"].items()}}
                       for r in records],
        "cases": [r for r in records if r["interesting"]],
    }
    if args.compare_with:
        report["reproducibility"] = compare_reports(json.loads(Path(args.compare_with).read_text()),
                                                    report)
    path = args.out / "report.json"
    path.write_text(json.dumps(report, indent=2) + "\n")
    print_summary(report)
    print(path)
    return 0


def compare_reports(old, new):
    o = {c["name"]: c for c in old["case_index"]}
    n = {c["name"]: c for c in new["case_index"]}
    common = sorted(set(o) & set(n))
    src = [k for k in common if o[k]["sha256"] != n[k]["sha256"]]
    stat = [k for k in common if o[k]["statuses"] != n[k]["statuses"]]
    return {"previous": old.get("started"), "previous_cases": len(o), "cases": len(n),
            "common_cases": len(common), "source_differences": src,
            "status_differences": stat,
            # identical on the cases both runs share (a rerun may cover a prefix)
            "identical": bool(common) and not src and not stat}


def print_summary(report):
    names = list(report["summary"])
    cols = [s for s in STATUSES if any(report["summary"][n][s] for n in names)]
    print(f"suite={report['suite']} target={report.get('target')} seed={report['seed']} "
          f"cases={report['count']} "
          f"seconds={report['seconds']}")
    print("toolchain".ljust(12) + "".join(c.rjust(17) for c in cols)
          + ("   oracle agree/disagree" if report["oracle_summary"] else ""))
    for n in names:
        line = n.ljust(12) + "".join(str(report["summary"][n][c]).rjust(17) for c in cols)
        if report["oracle_summary"]:
            o = report["oracle_summary"][n]
            line += f"   {o['agree']}/{o['disagree']}"
        print(line)
    if report["reference_failures"]:
        print(f"reference failures: {len(report['reference_failures'])}")
    for l in report["leads"][:20]:
        print("lead:", json.dumps(l))
    if len(report["leads"]) > 20:
        print(f"... {len(report['leads']) - 20} more leads")
    if "reproducibility" in report:
        print("reproducibility:", json.dumps({k: v for k, v in report["reproducibility"].items()
                                              if k != "status_differences"}))


def parse_kv(items, what):
    out = {}
    for item in items:
        if "=" not in item:
            raise SystemExit(f"{what}: expected NAME=VALUE, got {item!r}")
        k, v = item.split("=", 1)
        out[k] = v
    return out


def select_adapters(args):
    paths = parse_kv(args.path, "--path")
    tool_env = {}
    for item in args.tool_env:
        if ":" not in item or "=" not in item:
            raise SystemExit(f"--tool-env: expected NAME:KEY=VALUE, got {item!r}")
        name, kv = item.split(":", 1)
        k, v = kv.split("=", 1)
        tool_env.setdefault(name, {})[k] = os.path.expanduser(v)
    adapters = default_adapters()
    for label, exe in parse_kv(args.extra_gc, "--extra-gc").items():
        adapters.append(Adapter(label, "gc", "", exe, extra_env=dict(GC_ENV)))
        paths[label] = exe
    apply_cross_options(adapters, parse_kv(args.run_prefix, "--run-prefix"),
                        parse_kv(args.extra_flags, "--extra-flags"))
    detect(adapters, paths, tool_env)
    if args.toolchains:
        wanted = [t for t in args.toolchains.split(",") if t]
        known = {a.name for a in adapters}
        unknown = sorted(set(wanted) - known)
        if unknown:
            raise SystemExit(f"unknown toolchains: {', '.join(unknown)} (known: {', '.join(sorted(known))})")
        chosen = [a for a in adapters if a.name in wanted]
    else:
        chosen = adapters
    missing = [a for a in chosen if not a.available]
    for a in missing:
        print(f"warning: {a.name} unavailable ({a.reason})", file=sys.stderr)
    if missing and args.toolchains and not args.allow_missing:
        raise SystemExit("requested toolchains are unavailable (use --allow-missing)")
    return [a for a in chosen if a.available]


def cmd_list(args):
    args.toolchains, args.allow_missing = None, True
    adapters = select_adapters(args)
    names = {a.name for a in adapters}
    for a in default_adapters():
        if a.name not in names:
            print(f"{a.name:12} unavailable")
    for a in adapters:
        print(f"{a.name:12} {a.exe}  {a.version}")
    return 0


def cmd_gen(args):
    if args.suite == "directed":
        for name, prog, mode in directed_cases():
            if args.name in (None, name):
                print(f"// case {name} ({mode})\n{prog.source}")
        return 0
    prog = random_program(args.suite, args.seed, args.index, args.funcs, args.loops,
                          args.pairs, args.depth, args.word_bits, args.inputs)
    sys.stdout.write(prog.source)
    if args.records:
        Path(args.records).write_text(json.dumps(prog.records))
    return 0


def add_common(p):
    p.add_argument("--path", action="append", default=[], metavar="NAME=EXE",
                   help="executable for a toolchain or family (gc, gccgo, tinygo, llgo, yaegi)")
    p.add_argument("--tool-env", action="append", default=[], metavar="NAME:KEY=VALUE",
                   help="extra environment for one toolchain or family (build and run)")
    p.add_argument("--extra-gc", action="append", default=[], metavar="LABEL=EXE",
                   help="additional gc toolchain, e.g. gc-tip=~/go-tip/bin/go")
    p.add_argument("--run-prefix", action="append", default=[], metavar="NAME=CMD",
                   help="command prepended to compiled binaries of a toolchain or family, "
                        "e.g. gc=qemu-aarch64 (cross-target runs)")
    p.add_argument("--extra-flags", action="append", default=[], metavar="NAME=FLAGS",
                   help="flags appended to the build of a toolchain or family, e.g. gccgo=-static")
    p.add_argument("--target", default="native",
                   help="label of the target recorded in report.json, e.g. linux/arm64")


def add_gen(p):
    p.add_argument("--suite", choices=SUITES, default="core")
    p.add_argument("--seed", type=int, default=1)
    p.add_argument("--funcs", type=int, default=10, help="oracle-checked functions per program")
    p.add_argument("--loops", type=int, default=2, help="loop functions per program")
    p.add_argument("--pairs", type=int, default=6, help="input pairs per function")
    p.add_argument("--depth", type=int, default=3, help="maximum expression depth")
    p.add_argument("--word-bits", type=int, choices=(32, 64), default=64,
                   help="size of uint on the target (32 for arm, mipsle, 386...)")
    p.add_argument("--inputs", choices=("pool", "smt", "mixed"), default="pool",
                   help="input selection: a shared random pool (default), per-function "
                        "inputs chosen by z3 on semantic boundaries, or half of each "
                        "(smt and mixed need the z3 module)")


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="cmd", required=True)
    pl = sub.add_parser("list", help="detect toolchains and print their versions")
    add_common(pl)
    pg = sub.add_parser("gen", help="print one generated program")
    add_gen(pg)
    pg.add_argument("--index", type=int, default=0)
    pg.add_argument("--name", help="directed case name")
    pg.add_argument("--records", help="also write the oracle RPN records to this file")
    pr = sub.add_parser("run", help="run a campaign and write OUT/report.json")
    add_common(pr)
    add_gen(pr)
    pr.add_argument("--count", type=int, default=50)
    pr.add_argument("--start", type=int, default=0, help="first program index")
    pr.add_argument("--out", required=True, help="output directory (relative or absolute)")
    pr.add_argument("--toolchains", help="comma-separated subset (default: all detected)")
    pr.add_argument("--allow-missing", action="store_true",
                    help="skip requested toolchains that are not available")
    pr.add_argument("--reference", default="gc")
    pr.add_argument("--oracle", help="Lean oracle executable (lake exe oracle binary)")
    pr.add_argument("--jobs", type=int, default=os.cpu_count() or 1)
    pr.add_argument("--build-timeout", type=float, default=300)
    pr.add_argument("--run-timeout", type=float, default=60)
    pr.add_argument("--keep-all", action="store_true", help="keep clean case directories")
    pr.add_argument("--compare-with", help="previous report.json to check reproducibility")
    pr.add_argument("--progress", type=int, default=0, help="print progress every N cases")
    args = parser.parse_args(argv)
    return {"list": cmd_list, "gen": cmd_gen, "run": cmd_run}[args.cmd](args)


if __name__ == "__main__":
    raise SystemExit(main())
