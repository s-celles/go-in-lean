#!/usr/bin/env python3
"""Tests for smt_inputs.py (stdlib unittest; skipped without the z3 module).

Run: python3 -m unittest scripts/test_smt_inputs.py
The cross-check against gc needs a `go` on PATH (or $GO) and is skipped otherwise.
"""

import os
from pathlib import Path
import random
import re
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import alt_compiler_diff as acd  # noqa: E402

try:
    import z3  # noqa: F401
    import smt_inputs as si
    HAVE_Z3 = True
except ImportError:  # pragma: no cover - depends on the environment
    HAVE_Z3 = False

M64 = (1 << 64) - 1


def lit(t, v):
    return acd.lit(t, v)


def var(t, which="x"):
    return acd.var(t, which)


U8, S8, U16, S16, U32, S32, U64, S64 = ((8, False), (8, True), (16, False), (16, True),
                                        (32, False), (32, True), (64, False), (64, True))


@unittest.skipUnless(HAVE_Z3, "z3 module not available")
class EvalTests(unittest.TestCase):
    """The z3 encoding follows the Go specification on hand-picked cases."""

    def ev(self, n, x=0, y=0):
        return si.evaluate(n, x, y)

    def test_wraparound_and_conversions(self):
        self.assertEqual(self.ev({"k": "bin", "op": "add", "a": var(U8), "b": lit(U8, 1)}, 255), 0)
        # int8(-1) -> uint64 sign-extends, uint8(255) -> int64 does not
        self.assertEqual(self.ev({"k": "conv", "t": U64, "a": var(S8)}, 0xFF), M64)
        self.assertEqual(self.ev({"k": "conv", "t": S64, "a": var(U8)}, 0xFF), 0xFF)
        self.assertEqual(self.ev({"k": "conv", "t": U16, "a": var(U64)}, 0x12345), 0x2345)

    def test_shifts(self):
        shr = lambda t, c: {"k": "bin", "op": "shr", "a": var(t), "b": lit(U64, c)}  # noqa: E731
        shl = lambda t, c: {"k": "bin", "op": "shl", "a": var(t), "b": lit(U64, c)}  # noqa: E731
        self.assertEqual(self.ev(shr(S16, 32), 0x8000), 0xFFFF)  # int16 >> 32 = -1
        self.assertEqual(self.ev(shr(U16, 32), 0x8000), 0)
        self.assertEqual(self.ev(shr(S8, 1), 0x80), 0xC0)
        self.assertEqual(self.ev(shl(U8, 8), 0xFF), 0)
        self.assertEqual(self.ev(shl(U8, 3), 0xFF), 0xF8)
        huge = {"k": "bin", "op": "shr", "a": var(S32), "b": lit(U64, 1 << 63)}
        self.assertEqual(self.ev(huge, 0x80000000), 0xFFFFFFFF)

    def test_division_truncates_toward_zero(self):
        div = lambda t, op: {"k": "bin", "op": op, "a": var(t, "x"), "b": var(t, "y")}  # noqa: E731
        self.assertEqual(self.ev(div(S8, "div"), 0xF9, 2), 0xFD)  # -7/2 = -3
        self.assertEqual(self.ev(div(S8, "mod"), 0xF9, 2), 0xFF)  # -7%2 = -1
        self.assertEqual(self.ev(div(S8, "div"), 0x80, 0xFF), 0x80)  # -128/-1 = -128
        self.assertEqual(self.ev(div(S8, "mod"), 0x80, 0xFF), 0)
        self.assertEqual(self.ev(div(U8, "div"), 0xF9, 2), 0x7C)

    def test_comparisons_and_select(self):
        lt = {"k": "bin", "op": "lt", "a": var(S8, "x"), "b": var(S8, "y")}
        self.assertEqual(self.ev({"k": "conv", "t": U8, "a": lt}, 0xFF, 0), 1)  # -1 < 0
        ult = {"k": "bin", "op": "lt", "a": var(U8, "x"), "b": var(U8, "y")}
        self.assertEqual(self.ev({"k": "conv", "t": U8, "a": ult}, 0xFF, 0), 0)
        sel = {"k": "sel", "t": U8, "c": ult, "a": lit(U8, 7), "b": lit(U8, 9)}
        self.assertEqual(self.ev(sel, 1, 2), 7)
        self.assertEqual(self.ev(sel, 2, 1), 9)

    def test_math_bits(self):
        b = lambda op, w, t=None: {"k": "bits", "op": op, "w": w, "a": var((w, False))}  # noqa: E731
        self.assertEqual(self.ev(b("oc", 16), 0xF0F1), 9)
        self.assertEqual(self.ev(b("lz", 32), 1), 31)
        self.assertEqual(self.ev(b("lz", 8), 0), 8)
        self.assertEqual(self.ev(b("tz", 64), 0), 64)
        self.assertEqual(self.ev(b("tz", 16), 0x80), 7)
        self.assertEqual(self.ev(b("len", 8), 0x13), 5)
        self.assertEqual(self.ev(b("rev", 8), 0x55), 0xAA)
        self.assertEqual(self.ev(b("rev", 16), 1), 0x8000)
        self.assertEqual(self.ev(b("rb", 32), 0x11223344), 0x44332211)
        rot = {"k": "rot", "w": 8, "a": var(U8), "c": lit(S64, -1)}
        self.assertEqual(self.ev(rot, 0x01), 0x80)
        rot["c"] = lit(S64, 9)
        self.assertEqual(self.ev(rot, 0x81), 0x03)


@unittest.skipUnless(HAVE_Z3, "z3 module not available")
class PairTests(unittest.TestCase):
    def test_targets_hit_shift_boundary(self):
        # the count y reaches the width boundary in at least one pair
        n = {"k": "bin", "op": "shr", "a": var(S32, "x"), "b": var(U64, "y")}
        pairs, labels = si.smt_pairs(n, 8, random.Random(1))
        self.assertTrue(any(y in (31, 32) for _, y in pairs), pairs)
        self.assertTrue(labels)

    def test_targets_hit_signed_division_overflow(self):
        n = {"k": "bin", "op": "div", "a": var(S16, "x"), "b": var(S16, "y")}
        pairs, _ = si.smt_pairs(n, 10, random.Random(2))
        self.assertIn((0x8000, 0xFFFF), [(x & 0xFFFF, y & 0xFFFF) for x, y in pairs])

    def test_guard_path_condition(self):
        # inside the guarded arm the divisor is never zero
        g = random.Random(3)
        gen = acd.SubsetGen(g, with_bits=False)
        b = var(U8, "y")
        guarded = {"k": "bin", "op": "mod", "a": var(U8, "x"), "b": gen.nonzero(b, U8)}
        pairs, _ = si.smt_pairs(guarded, 10, random.Random(4))
        self.assertTrue(pairs)
        self.assertEqual(len(pairs), len(set(pairs)))

    def test_deterministic(self):
        r = random.Random("t")
        gen = acd.SubsetGen(r, with_bits=True)
        t = gen.build(U32, 3)
        a = si.smt_pairs(t, 8, random.Random(5))
        b = si.smt_pairs(t, 8, random.Random(5))
        self.assertEqual(a, b)

    def test_program_inputs_smt_keeps_trees(self):
        pool = acd.random_program("core", 7, 3, npairs=8)
        smt = acd.random_program("core", 7, 3, inputs="smt", npairs=8)
        strip = lambda s: re.sub(r"\n\tfmt\.Printf.*|var gin = .*|in\[\d+\]\[\d\]", "", s)  # noqa: E731
        fp = re.findall(r"func v\d+\(x, y uint64\) uint64 \{.*?\n\}", pool.source, re.S)
        fs = re.findall(r"func v\d+\(x, y uint64\) uint64 \{.*?\n\}", smt.source, re.S)
        self.assertEqual(fp, fs)
        self.assertNotEqual(strip(pool.source), "")
        self.assertEqual(smt.meta["inputs"], "smt")
        per_func = {}
        for r in smt.records:
            per_func.setdefault(r["e"], []).append((r["x"], r["y"]))
        self.assertEqual(len(per_func), 10)
        self.assertTrue(all(len(v) == 8 for v in per_func.values()))
        # every record has a matching output line
        for r in smt.records:
            self.assertIn(f'e={r["e"]} x={r["x"]} y={r["y"]} OK', smt.source)

    def test_pool_mode_unchanged(self):
        a = acd.random_program("bits", 11, 4)
        b = acd.random_program("bits", 11, 4, inputs="pool")
        self.assertEqual(a.source, b.source)


def go_exe():
    g = os.environ.get("GO") or shutil.which("go")
    return g if g and os.access(g, os.X_OK) else None


@unittest.skipUnless(HAVE_Z3 and go_exe(), "needs z3 and a go toolchain")
class AgainstGcTests(unittest.TestCase):
    """The encoding agrees with gc (amd64) on generated programs."""

    def test_random_programs(self):
        for suite, idx in (("core", 0), ("core", 1), ("bits", 0), ("bits", 1)):
            prog = acd.random_program(suite, 20261106, idx, inputs="smt", npairs=6)
            with tempfile.TemporaryDirectory() as d:
                Path(d, "main.go").write_text(prog.source)
                Path(d, "go.mod").write_text("module m\ngo 1.21\n")
                env = dict(os.environ, GOFLAGS="-mod=mod", GO111MODULE="on")
                out = subprocess.run([go_exe(), "run", "."], cwd=d, env=env, text=True,
                                     capture_output=True, timeout=300)
                self.assertEqual(out.returncode, 0, out.stderr)
            got = {}
            for line in out.stdout.splitlines():
                m = re.match(r"e=(\d+) x=(\d+) y=(\d+) OK (\d+)", line)
                if m:
                    got[tuple(int(v) for v in m.groups()[:3])] = int(m.group(4))
            for r in prog.records:
                tree = prog.trees[r["e"]]
                want = si.evaluate(tree, r["x"], r["y"])
                want64 = si.as_uint64(tree, want)
                self.assertEqual(got[(r["e"], r["x"], r["y"])], want64,
                                 f"{suite}/{idx} e={r['e']} x={r['x']} y={r['y']}")


if __name__ == "__main__":
    unittest.main()
