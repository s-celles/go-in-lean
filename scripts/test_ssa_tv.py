#!/usr/bin/env python3
"""Tests for ssa_tv.py (stdlib unittest; skipped without the z3 module).

Run: python3 -m unittest scripts/test_ssa_tv.py
The tests that compile Go need a `go` on PATH (or $GO) and are skipped otherwise.
"""

import os
from pathlib import Path
import random
import shutil
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

try:
    import z3  # noqa: F401
    import ssa_tv as tv
    HAVE_Z3 = True
except ImportError:  # pragma: no cover - depends on the environment
    HAVE_Z3 = False

GO = os.environ.get("GO") or shutil.which("go")
M64 = (1 << 64) - 1

# The `build` dump of
#   func v4(x, y uint64) uint64 {
#       t1 := (int16(y) & int16(2)) >> uint64(3)
#       var r int16 = 5
#       if int8(x) < int8(y) { r = t1 ^ int16(x) }
#       return uint64(r)
#   }
BUILD = """\
v4 func(uint64, uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (-4) v7 = Arg <uint64> {x} (x[uint64])
    (-4) v8 = Arg <uint64> {y} (y[uint64])
    (5) v10 = Trunc64to16 <int16> v8
    (?) v11 = Const16 <int16> [2]
    (5) v12 = And16 <int16> v10 v11
    (?) v13 = Const64 <uint64> [3]
    (5) v14 = Rsh16x64 <int16> [false] v12 v13 (t1[int16])
    (?) v15 = Const16 <int16> [5] (r[int16])
    (7) v16 = Trunc64to8 <int8> v7
    (7) v17 = Trunc64to8 <int8> v8
    (7) v18 = Less8 <bool> v16 v17
    If v18 -> b3 b2
  b2: <- b1 b3
    (10) v23 = Phi <int16> v15 v22 (r[int16])
    (10) v24 = SignExt16to64 <uint64> v23
    (-10) v25 = Copy <mem> v1
    (10) v26 = MakeResult <uint64,mem> v24 v25
    Ret v26
  b3: <- b1
    (-8) v19 = Copy <int16> v14 (t1[int16])
    (-8) v20 = Copy <uint64> v7 (x[uint64])
    (8) v21 = Trunc64to16 <int16> v20
    (8) v22 = Xor16 <int16> v19 v21 (r[int16])
    Plain -> b2
name x[uint64]: [v7 v20]
name y[uint64]: [v8]
"""

# The same function after the generic passes (branch turned into CondSelect,
# (y&2)>>3 folded to 0, register arguments).
LATE = """\
v4 func(uint64, uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (7) v7 = ArgIntReg <uint64> {x+0} [0] (x[uint64])
    (7) v8 = ArgIntReg <uint64> {y+0} [1] (y[uint64])
    (?) v15 = Const16 <int16> [5] (r[int16])
    (+7) v16 = Trunc64to8 <int8> v7
    (7) v17 = Trunc64to8 <int8> v8
    (7) v18 = Less8 <bool> v16 v17
    (+8) v21 = Trunc64to16 <int16> v7
    (10) v23 = CondSelect <int16> v21 v15 v18 (r[int16])
    (+10) v24 = SignExt16to64 <uint64> v23
    (10) v26 = MakeResult <uint64,mem> v24 v1
    Ret v26
name x[uint64]: [v7]
"""

# A division with its zero check, and a shift whose count is claimed bounded.
DIV = """\
d func(uint64, uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (3) v7 = Arg <uint64> {x}
    (3) v8 = Arg <uint64> {y}
    (4) v9 = Trunc64to32 <int32> v7
    (4) v10 = Trunc64to32 <int32> v8
    (?) v11 = Const32 <int32> [0]
    (4) v12 = Neq32 <bool> v10 v11
    If v12 -> b2 b3 (likely)
  b2: <- b1
    (4) v13 = Div32 <int32> [false] v9 v10
    (4) v14 = Rsh32x64 <int32> [BOUNDED] v13 v8
    (4) v15 = SignExt32to64 <uint64> v14
    (4) v16 = MakeResult <uint64,mem> v15 v1
    Ret v16
  b3: <- b1
    (4) v17 = StaticLECall <mem> {AuxCall{runtime.panicdivide}} v1
    Exit v17
"""


def v4_ref(x, y):
    """Go semantics of v4, for the evaluation tests."""
    def s(v, w):
        v &= (1 << w) - 1
        return v - (1 << w) if v >> (w - 1) else v
    t1 = s(y, 16) & 2
    t1 >>= 3
    r = 5
    if s(x, 8) < s(y, 8):
        r = s(t1 ^ s(x, 16), 16)
    return r & M64


@unittest.skipUnless(HAVE_Z3, "z3 module not available")
class ParseTests(unittest.TestCase):
    def test_blocks_values_and_controls(self):
        f = tv.parse_dump(BUILD)
        self.assertEqual(f.name, "v4")
        self.assertEqual([b.name for b in f.blocks], ["b1", "b2", "b3"])
        b2 = f.block("b2")
        self.assertEqual(b2.preds, ["b1", "b3"])
        self.assertEqual(b2.kind, "Ret")
        b1 = f.block("b1")
        self.assertEqual((b1.kind, b1.controls, b1.succs), ("If", ["v18"], ["b3", "b2"]))
        v14 = f.values["v14"]
        self.assertEqual((v14.op, v14.type, v14.auxint, v14.args), ("Rsh16x64", "int16", "false", ["v12", "v13"]))
        self.assertEqual(f.values["v7"].aux, "x")

    def test_register_arguments_and_calls(self):
        f = tv.parse_dump(LATE)
        self.assertEqual((f.values["v7"].op, f.values["v7"].aux, f.values["v7"].auxint), ("ArgIntReg", "x+0", "0"))
        d = tv.parse_dump(DIV)
        self.assertEqual(d.values["v17"].aux, "AuxCall{runtime.panicdivide}")
        self.assertEqual(d.block("b3").kind, "Exit")
        self.assertEqual(d.block("b1").succs, ["b2", "b3"])


@unittest.skipUnless(HAVE_Z3, "z3 module not available")
class SemanticsTests(unittest.TestCase):
    def test_evaluate_matches_go_semantics(self):
        rng = random.Random(1)
        pts = [(0, 0), (0x80, 0x7F), (0x7F, 0x80), (0xFFFF, 1), (1, 0xFF)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(20)]
        for dump in (BUILD, LATE):
            f = tv.parse_dump(dump)
            for x, y in pts:
                self.assertEqual(tv.evaluate(f, {"x": x, "y": y}), ("ret", v4_ref(x, y)), (dump[:12], x, y))

    def test_panic_outcome(self):
        f = tv.parse_dump(DIV.replace("[BOUNDED]", "[false]"))
        self.assertEqual(tv.evaluate(f, {"x": 7, "y": 0}), ("panic:runtime.panicdivide", 0))
        # int32(-8) / 2 = -4, then >> 2 (count 2 < 32) = -1
        self.assertEqual(tv.evaluate(f, {"x": (-8) & M64, "y": 2}), ("ret", M64))
        # count 40 >= 32: sign fill
        self.assertEqual(tv.evaluate(f, {"x": (-800) & M64, "y": 40}), ("ret", M64))
        self.assertEqual(tv.evaluate(f, {"x": 8, "y": 40}), ("ret", 0))

    def test_shift_semantics(self):
        for op, w, signed, left in (("Lsh8x64", 8, False, True), ("Rsh16Ux8", 16, False, False),
                                    ("Rsh32x16", 32, True, False), ("Lsh64x32", 64, False, True)):
            cw = int(op.split("x")[1])
            src = f"""\
s func(uint64, uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (3) v7 = Arg <uint64> {{x}}
    (3) v8 = Arg <uint64> {{y}}
    (4) v9 = {"Copy" if w == 64 else f"Trunc64to{w}"} <int{w}> v7
    (4) v10 = {"Copy" if cw == 64 else f"Trunc64to{cw}"} <uint{cw}> v8
    (4) v11 = {op} <int{w}> [false] v9 v10
    (4) v12 = {"Copy" if w == 64 else ("SignExt" if signed else "ZeroExt") + f"{w}to64"} <uint64> v11
    (4) v13 = MakeResult <uint64,mem> v12 v1
    Ret v13
"""
            f = tv.parse_dump(src)
            for x in (1, 0x80, (1 << (w - 1)) | 5, (1 << w) - 1):
                for c in (0, 1, w - 1, w, w + 1, (1 << cw) - 1):
                    xv = x & ((1 << w) - 1)
                    if c >= w:
                        r = (((1 << w) - 1) if (signed and xv >> (w - 1)) else 0)
                    elif left:
                        r = (xv << c) & ((1 << w) - 1)
                    elif signed and xv >> (w - 1):
                        r = ((xv - (1 << w)) >> c) & ((1 << w) - 1)
                    else:
                        r = xv >> c
                    if signed and r >> (w - 1):
                        r = (r - (1 << w)) & M64
                    self.assertEqual(tv.evaluate(f, {"x": x, "y": c}), ("ret", r), (op, x, c))

    def test_unsupported_op_raises(self):
        with self.assertRaises(tv.Unsupported):
            tv.evaluate(tv.parse_dump(BUILD.replace("Xor16", "Frobnicate16")), {"x": 1, "y": 2})


@unittest.skipUnless(HAVE_Z3, "z3 module not available")
class CheckTests(unittest.TestCase):
    def test_equivalent_passes(self):
        self.assertIsNone(tv.equivalent(tv.parse_dump(BUILD), tv.parse_dump(LATE)))

    def test_counterexample_for_a_wrong_pass(self):
        bad = LATE.replace("Const16 <int16> [5]", "Const16 <int16> [6]")
        cex = tv.equivalent(tv.parse_dump(BUILD), tv.parse_dump(bad))
        self.assertIsNotNone(cex)
        a = tv.evaluate(tv.parse_dump(BUILD), cex)
        b = tv.evaluate(tv.parse_dump(bad), cex)
        self.assertNotEqual(a, b)

    def test_panic_kind_is_part_of_the_outcome(self):
        other = DIV.replace("runtime.panicdivide", "runtime.panicshift").replace("[BOUNDED]", "[false]")
        cex = tv.equivalent(tv.parse_dump(DIV.replace("[BOUNDED]", "[false]")), tv.parse_dump(other))
        self.assertIsNotNone(cex)
        self.assertEqual(cex["y"] & 0xFFFFFFFF, 0)

    def test_bounded_shift_obligation(self):
        bad = tv.obligations(tv.parse_dump(DIV.replace("[BOUNDED]", "[true]")))
        self.assertEqual([o["value"] for o in bad], ["v14"])
        self.assertGreaterEqual(bad[0]["inputs"]["y"], 32)
        self.assertEqual(tv.obligations(tv.parse_dump(DIV.replace("[BOUNDED]", "[false]"))), [])

    def test_division_obligations(self):
        # The zero check guards the division: no obligation fails.
        self.assertEqual(tv.obligations(tv.parse_dump(DIV.replace("[BOUNDED]", "[false]"))), [])
        # Claiming the divisor is not -1 (Div32 [true]) is wrong for MinInt / -1.
        bad = tv.obligations(tv.parse_dump(
            DIV.replace("[BOUNDED]", "[false]").replace("Div32 <int32> [false]", "Div32 <int32> [true]")))
        self.assertEqual([o["value"] for o in bad], ["v13"])
        self.assertEqual(bad[0]["inputs"]["x"] & 0xFFFFFFFF, 0x80000000)
        self.assertEqual(bad[0]["inputs"]["y"] & 0xFFFFFFFF, 0xFFFFFFFF)
        # Dropping the guard exposes a division by zero.
        unguarded = DIV.replace("[BOUNDED]", "[false]").replace("If v12 -> b2 b3 (likely)", "Plain -> b2")
        bad = tv.obligations(tv.parse_dump(unguarded))
        self.assertEqual([o["value"] for o in bad], ["v13"])

    def test_ill_typed_values(self):
        # golang/go#82767 on tip: opt folds two shift counts into Const64 <int32>.
        bad = BUILD.replace("Const64 <uint64> [3]", "Const64 <int32> [4611686018427387905]")
        # The constant itself, and the shift that takes it as a 64-bit count.
        self.assertEqual([(o["value"], o["op"]) for o in tv.ill_typed(tv.parse_dump(bad))],
                         [("v13", "Const64"), ("v14", "Rsh16x64")])
        self.assertEqual(tv.ill_typed(tv.parse_dump(BUILD)), [])
        self.assertEqual(tv.ill_typed(tv.parse_dump(LATE)), [])
        rep = tv.validate([("build", BUILD), ("opt", bad)])
        self.assertEqual([(f["kind"], f["pass"]) for f in rep["failures"]], [("type", "opt")] * 2)
        # The same mistyping is harmless when the constant fits the narrow type.
        ok = BUILD.replace("Const64 <uint64> [3]", "Const64 <int32> [3]")
        rep = tv.validate([("build", BUILD), ("opt", ok)])
        self.assertEqual((rep["failures"], rep["benign"]), ([], 2))

    def test_ill_typed_byte_and_bit_reversal(self):
        # golang/go#82873 (BitRev8 <int>, go1.26 arm64) and #82782 (Bswap16 <uint>, power10).
        for op in ("BitRev8", "Bswap16"):
            w = int(op[-2:] if op.endswith("16") else op[-1])
            src = BUILD.replace("(5) v10 = Trunc64to16 <int16> v8",
                                f"(5) v9 = Trunc64to{w} <uint{w}> v8\n    (5) v10 = {op} <int> v9")
            got = [(o["value"], o["op"]) for o in tv.ill_typed(tv.parse_dump(src))]
            self.assertIn(("v10", op), got)

    def test_phi_edge_from_a_deleted_block(self):
        # prove deletes b3 but leaves it in b2's predecessors and v22 in the Phi.
        src = BUILD.replace("If v18 -> b3 b2", "First -> b2 b3")
        src = src[:src.index("  b3: <- b1")] + "name x[uint64]: [v7]\n"
        f = tv.parse_dump(src)
        self.assertEqual(tv.evaluate(f, {"x": 1, "y": 2}), ("ret", 5))
        self.assertEqual(tv.obligations(f), [])

    def test_entry_block_not_listed_first(self):
        # After early_fuse the entry block can come after the others in the dump.
        b1 = BUILD[BUILD.index("  b1:"):BUILD.index("  b2:")]
        rest = BUILD[BUILD.index("  b2:"):BUILD.index("name ")]
        moved = BUILD.splitlines()[0] + "\n" + rest + b1
        f = tv.parse_dump(moved)
        self.assertEqual(f.entry().name, "b1")
        for x, y in ((0x80, 0x7F), (0x7F, 0x80)):
            self.assertEqual(tv.evaluate(f, {"x": x, "y": y}), ("ret", v4_ref(x, y)))

    def test_opaque_string_constant(self):
        src = BUILD.replace("    (?) v15 = Const16", '    (?) v99 = ConstString <string> {"[\\x00"}\n    (?) v15 = Const16')
        f = tv.parse_dump(src)
        self.assertEqual(f.values["v99"].op, "ConstString")
        with self.assertRaises(tv.Unsupported):
            tv.evaluate(f, {"x": 1, "y": 2})

    def test_narrow_type_that_fits_is_benign(self):
        # divmod.rules types the 32-bit shifts of an int8 division by a constant as int8:
        # sound, because the value always fits. The same shape with a value that does not
        # fit (an int8-typed 32-bit shift by 1 of an arbitrary 32-bit value) is reported.
        tmpl = """\
d func(uint64, uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (3) v7 = Arg <uint64> {x}
    (4) v8 = Trunc64to8 <int8> v7
    (4) v9 = SignExt8to32 <int32> v8
    (4) v10 = Trunc64to32 <int32> v7
    (?) v11 = Const64 <uint64> [SHIFT]
    (4) v12 = Rsh32x64 <int8> SRC v11
    (4) v13 = SignExt8to64 <uint64> v12
    (4) v14 = MakeResult <uint64,mem> v13 v1
    Ret v14
"""
        good = tv.parse_dump(tmpl.replace("SRC", "v9").replace("SHIFT", "2"))
        bad = tv.parse_dump(tmpl.replace("SRC", "v10").replace("SHIFT", "1"))
        self.assertEqual([o["value"] for o in tv.ill_typed(good)], ["v12"])
        self.assertEqual(tv.validate([("build", tmpl.replace("SRC", "v9").replace("SHIFT", "2"))])["failures"], [])
        rep = tv.validate([("build", tmpl.replace("SRC", "v10").replace("SHIFT", "1"))])
        self.assertEqual([(f["kind"], f["value"]) for f in rep["failures"]], [("type", "v12")])
        self.assertEqual(tv.validate([("build", tmpl.replace("SRC", "v9").replace("SHIFT", "2"))])["benign"], 1)
        del good, bad

    def test_word_size(self):
        src = BUILD.replace("(?) v15 = Const16 <int16> [5]", "(?) v99 = Const32 <int> [7]\n    (?) v15 = Const16 <int16> [5]")
        self.assertEqual(len(tv.ill_typed(tv.parse_dump(src))), 1)
        self.assertEqual(tv.ill_typed(tv.parse_dump(src), word_bits=32), [])

    def test_loops_are_unsupported(self):
        loop = BUILD.replace("Plain -> b2\n", "Plain -> b1\n").replace("  b3: <- b1", "  b3: <- b1")
        loop = loop.replace("  b1:\n", "  b1: <- b3\n")
        with self.assertRaises(tv.Unsupported):
            tv.evaluate(tv.parse_dump(loop), {"x": 1, "y": 1})


GO_SRC = """\
package main

import (
	"fmt"
	"math/bits"
	"os"
	"strconv"
)

//go:noinline
func f0(x, y uint64) uint64 { return uint64(int8(x) / int8(y|1)) }

//go:noinline
func f1(x, y uint64) uint64 { return uint64(int32(x) >> (y & 63)) }

//go:noinline
func f2(x, y uint64) uint64 {
	r := uint16(x) << uint8(y)
	if int16(r) < int16(y) {
		r ^= 0x8001
	}
	return uint64(r)
}

//go:noinline
func f3(x, y uint64) uint64 { return uint64(bits.Len64(x)) + uint64(bits.RotateLeft64(y, 5)) }

//go:noinline
func f4(x, y uint64) uint64 { return uint64(int64(x)%7) ^ uint64(uint32(y)/3) }

//go:noinline
func f5(x, y uint64) uint64 { return uint64(int16(x) * -3 >> 1) }

func main() {
	fs := []func(uint64, uint64) uint64{f0, f1, f2, f3, f4, f5}
	x, _ := strconv.ParseUint(os.Args[1], 10, 64)
	y, _ := strconv.ParseUint(os.Args[2], 10, 64)
	for _, f := range fs {
		fmt.Println(f(x, y))
	}
}
"""


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class AgainstGcTests(unittest.TestCase):
    """The encoding of every generic pass agrees with the compiled program."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_"))
        (cls.tmp / "main.go").write_text(GO_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-o", "prog", "."], cwd=cls.tmp, check=True)
        cls.passes = {f"f{i}": tv.dump_passes(GO, cls.tmp, f"f{i}") for i in range(6)}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_passes_are_generic_only(self):
        names = [p for p, _ in self.passes["f0"]]
        self.assertEqual(names[0], "build")
        self.assertIn("prove", names)
        self.assertNotIn("lower", names)

    def test_evaluation_matches_gc(self):
        rng = random.Random(3)
        pts = [(0, 0), (M64, M64), (0x80, 0xFF), (1 << 63, 64), (0xFFFF8000, 1)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(6)]
        for x, y in pts:
            out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                                 text=True, check=True).stdout.split()
            for i in range(6):
                for name, dump in (self.passes[f"f{i}"][0], self.passes[f"f{i}"][-1]):
                    got = tv.evaluate(tv.parse_dump(dump), {"x": x, "y": y})
                    self.assertEqual(got, ("ret", int(out[i])), (f"f{i}", name, x, y))

    def test_validate_reports_no_failure(self):
        for fn, passes in self.passes.items():
            rep = tv.validate(passes)
            self.assertEqual(rep["failures"], [], fn)
            self.assertGreater(rep["checked"], 0, fn)


PPC_SRC = GO_SRC.replace("func main() {", """//go:noinline
func f6(x, y uint64) uint64 { return uint64(int32(int16(int32(x) >> 1))) }

//go:noinline
func f7(x, y uint64) uint64 { return uint64(int32(x)/int32(y|1)) ^ uint64(uint32(x)>>(y&31)) }

//go:noinline
func f8(x, y uint64) uint64 { return uint64(int64(x)%int64(y|2)) + uint64(uint32(x)%uint32(y|1)) }

//go:noinline
func f9(x, y uint64) uint64 {
	return uint64(bits.TrailingZeros64(x)) ^ bits.ReverseBytes64(y) ^ uint64(bits.ReverseBytes32(uint32(x)))
}

//go:noinline
func f10(x, y uint64) uint64 { return uint64(int32(x) % int32(y|1)) + uint64(int64(y) % int64(x|1)) }

func main() {""").replace("f0, f1, f2, f3, f4, f5}", "f0, f1, f2, f3, f4, f5, f6, f7, f8, f9, f10}")


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredPPC64Tests(unittest.TestCase):
    """Lowered ppc64 passes: machine semantics against the native (amd64) program."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_ppc_"))
        (cls.tmp / "main.go").write_text(PPC_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(11)]
        cls.dumps = {}
        for cpu in ("power8", "power9", "power10"):
            os.environ["GOPPC64"] = cpu
            try:
                cls.dumps[cpu] = tv.dump_passes(GO, cls.tmp, names, "ppc64le", lowered=True)
            finally:
                del os.environ["GOPPC64"]

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_lowered_passes_are_included(self):
        names = [p for p, _ in self.dumps["power8"]["f0"]]
        self.assertIn("lower", names)
        self.assertEqual(names[-1], "flagalloc")

    def test_lowered_evaluation_matches_gc(self):
        rng = random.Random(5)
        pts = [(1, 0), (M64, M64), (1 << 31, 0), (0x80000000, 1), (0xFFFF8000, 31), (65536, 7),
               (1 << 63, M64), (0x80000000, 0xFFFFFFFF)]  # MinInt % -1 for f10
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(5)]
        for x, y in pts:
            out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                                 text=True, check=True).stdout.split()
            for cpu, dumps in self.dumps.items():
                for i in range(11):
                    if i == 6:
                        continue  # f6 is miscompiled on ppc64 (golang/go#82775)
                    for name in ("lower", "flagalloc"):
                        f = tv.parse_dump(dict(dumps[f"f{i}"])[name])
                        f.arch = "ppc64le"
                        self.assertEqual(tv.evaluate(f, {"x": x, "y": y}), ("ret", int(out[i])),
                                         (cpu, f"f{i}", name, x, y))

    def test_finds_82775_at_lower(self):
        rep = tv.validate(self.dumps["power8"]["f6"], arch="ppc64le")
        eq = [fl for fl in rep["failures"] if fl["kind"] == "equivalence"]
        self.assertEqual([fl["pass"] for fl in eq], ["lower"])
        x = eq[0]["inputs"]["x"]
        want = (((x & 0xFFFFFFFF) >> 1) & 0xFFFF)
        want = (want - 0x10000 if want >> 15 else want) & M64
        self.assertEqual(eq[0]["before_out"], ("ret", want))
        self.assertNotEqual(eq[0]["after_out"], ("ret", want))

    def test_no_report_on_correct_functions(self):
        for cpu, dumps in self.dumps.items():
            for i in (0, 1, 2, 3, 4, 5, 7, 8, 9, 10):
                rep = tv.validate(dumps[f"f{i}"], arch="ppc64le")
                self.assertEqual((rep["failures"], rep["unsupported"]), ([], None), (cpu, f"f{i}"))


AMD_SRC = PPC_SRC.replace("func main() {", """//go:noinline
func f11(x, y uint64) uint64 { return uint64(uint32(x) &^ (uint32(x) ^ uint32(x))) }

//go:noinline
func b2i(b bool) uint64 {
	if b {
		return 1
	}
	return 0
}

//go:noinline
func f12(x, y uint64) uint64 {
	t := int8(x) >> (y & 7)
	if uint16(y) > uint16(x) {
		t ^= int8(b2i(int32(x) < int32(y)))
	}
	return uint64(t) + uint64(uint16(x)>>(y&15))
}

func main() {""").replace("f8, f9, f10}", "f8, f9, f10, f11, f12}")
AMD_N = 13


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredAMD64Tests(unittest.TestCase):
    """Lowered amd64 passes, optimized and -N, against the native program."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_amd_"))
        (cls.tmp / "main.go").write_text(AMD_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(AMD_N)]
        cls.dumps = {fl: tv.dump_passes(GO, cls.tmp, names, "amd64", lowered=True, gcflags=fl)
                     for fl in ("", "-N -l")}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_lowered_evaluation_matches_gc(self):
        rng = random.Random(9)
        pts = [(1, 0), (M64, M64), (1 << 31, 0), (0x80000000, 1), (0xFFFF8000, 31), (65536, 7),
               (1 << 63, M64), (0x80000000, 0xFFFFFFFF), (1 << 63 | 5, 3)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(4)]
        for x, y in pts:
            out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                                 text=True, check=True).stdout.split()
            for fl, dumps in self.dumps.items():
                for i in range(AMD_N):
                    if i == 11 and fl:
                        continue  # f11 is miscompiled with -N (golang/go#36897)
                    for name in ("writebarrier", "lower", "flagalloc"):
                        f = tv.parse_dump(dict(dumps[f"f{i}"])[name])
                        if name != "writebarrier":
                            f.arch = "amd64"
                        self.assertEqual(tv.evaluate(f, {"x": x, "y": y}), ("ret", int(out[i])),
                                         (fl, f"f{i}", name, x, y))

    def test_finds_36897_with_N(self):
        rep = tv.validate(self.dumps["-N -l"]["f11"], arch="amd64")
        eq = [fl for fl in rep["failures"] if fl["kind"] == "equivalence"]
        self.assertEqual([fl["pass"] for fl in eq], ["lower"])
        x = eq[0]["inputs"]["x"]
        self.assertEqual(eq[0]["before_out"], ("ret", x & 0xFFFFFFFF))
        self.assertEqual(eq[0]["after_out"], ("ret", x))
        self.assertEqual(tv.validate(self.dumps[""]["f11"], arch="amd64")["failures"], [])

    def test_no_report_on_correct_functions(self):
        for fl, dumps in self.dumps.items():
            for i in range(AMD_N):
                if i == 11 and fl:
                    continue
                rep = tv.validate(dumps[f"f{i}"], arch="amd64")
                self.assertEqual((rep["failures"], rep["unsupported"]), ([], None), (fl, f"f{i}"))


if __name__ == "__main__":
    unittest.main()
