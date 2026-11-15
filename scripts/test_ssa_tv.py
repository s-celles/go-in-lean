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


S390X_PRE = """\
szLessB func(int8) bool
  b1:
    (?) v1 = InitMem <mem>
    (+2) v6 = ArgIntReg <int8> {y+0} [0] (y[int8])
    (+2) v8 = SignExt8to64 <uint64> v6
    (?) v9 = Const64 <uint64> [4294967295]
    (2) v10 = Less64U <bool> v8 v9
    (2) v11 = MakeResult <bool,mem> v10 v1
    Ret v11
name y[int8]: [v6]
"""

S390X_LOWER = """\
szLessB func(int8) bool
  b1:
    (?) v1 = InitMem <mem>
    (+2) v6 = ArgIntReg <int8> {y+0} [0] (y[int8])
    (+2) v8 = MOVBreg <uint64> v6
    (2) v3 = MOVDconst <uint64> [0]
    (2) v4 = MOVDconst <uint64> [1]
    (2) v5 = CMPWUconst <flags> [-1] v8
    (2) v10 = LOCGR <bool> {Less} v3 v4 v5
    (2) v11 = MakeResult <bool,mem> v10 v1
    Ret v11
name y[int8]: [v6]
"""

S390X_CLEAN = S390X_LOWER.replace("CMPWUconst", "CMPUconst")

S390X_BRANCH = """\
s390Branch func(uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (2) v7 = ArgIntReg <uint64> {x+0} [0] (x[uint64])
    (?) v8 = MOVDconst <uint64> [0]
    (2) v9 = CMP <flags> v7 v8
    BRC {Less} v9 -> b2 b3
  b2: <- b1
    (3) v10 = MOVDconst <uint64> [1]
    (3) v11 = MakeResult <uint64,mem> v10 v1
    Ret v11
  b3: <- b1
    (3) v12 = MOVDconst <uint64> [0]
    (3) v13 = MakeResult <uint64,mem> v12 v1
    Ret v13
"""

S390X_SRC = """\
package main
import (
	"fmt"
	"os"
	"strconv"
)

func f0(x, y uint64) uint64 {
	if uint64(int8(y)) < 0xFFFFFFFF { return 1 }
	return 0
}
func f1(x, y uint64) uint64 {
	if uint64(int16(y)) <= 0xFFFFFFF0 { return 1 }
	return 0
}
func f2(x, y uint64) uint64 {
	if uint64(int8(y)) < 0xFFFFFFFFFFFFFFFF { return 1 }
	return 0
}
func f3(x, y uint64) uint64 { return (x + y) ^ (x & y) }

func main() {
	x, _ := strconv.ParseUint(os.Args[1], 0, 64)
	y, _ := strconv.ParseUint(os.Args[2], 0, 64)
	fmt.Printf("%d %d %d %d\\n", f0(x, y), f1(x, y), f2(x, y), f3(x, y))
}
"""

ARM64_PRE = """\
f0 func(int64, int64) int64
  b1:
    (?) v1 = InitMem <mem>
    (+2) v6 = ArgIntReg <int64> {x+0} [0] (x[int64])
    (+2) v7 = ArgIntReg <int64> {y+8} [1] (y[int64])
    (+2) v8 = Com64 <int64> v7
    (?) v9 = ConstBool <bool> [true]
    (2) v10 = CondSelect <int64> v8 v6 v9
    (2) v11 = MakeResult <int64,mem> v10 v1
    Ret v11
name x[int64]: [v6]
name y[int64]: [v7]
"""

ARM64_BAD = """\
f0 func(int64, int64) int64
  b1:
    (?) v1 = InitMem <mem>
    (+2) v7 = ArgIntReg <int64> {y+8} [1] (y[int64])
    (2) v8 = XORconst <int64> [1] v7
    (2) v9 = MakeResult <int64,mem> v8 v1
    Ret v9
name y[int64]: [v7]
"""

ARM64_FIXED = ARM64_BAD.replace("XORconst <int64> [1]", "MVN <int64>")

ARM64_BRANCH = """\
arm64Branch func(int64) int64
  b1:
    (?) v1 = InitMem <mem>
    (2) v2 = ArgIntReg <int64> {x+0} [0] (x[int64])
    (2) v3 = CMPconst <flags> [0] v2
    LT v3 -> b2 b3
  b2: <- b1
    (3) v4 = MOVDconst <int64> [1]
    (3) v5 = MakeResult <int64,mem> v4 v1
    Ret v5
  b3: <- b1
    (3) v6 = MOVDconst <int64> [0]
    (3) v7 = MakeResult <int64,mem> v6 v1
    Ret v7
"""

ARM64_MSUB = """\
arm64Msub func(uint64, uint64, uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (2) v2 = ArgIntReg <uint64> {x+0} [0] (x[uint64])
    (2) v3 = ArgIntReg <uint64> {y+8} [1] (y[uint64])
    (2) v4 = ArgIntReg <uint64> {z+16} [2] (z[uint64])
    (3) v5 = MSUB <uint64> v2 v3 v4
    (3) v6 = MakeResult <uint64,mem> v5 v1
    Ret v6
name x[uint64]: [v2]
name y[uint64]: [v3]
name z[uint64]: [v4]
"""

ARM64_MADD = ARM64_MSUB.replace("arm64Msub", "arm64Madd").replace(" = MSUB ", " = MADD ")

ARM64_MVN_BOOL = """\
arm64MvnBool func(bool) uint64
  b1:
    (?) v1 = InitMem <mem>
    (2) v2 = ArgIntReg <bool> {x+0} [0] (x[bool])
    (3) v3 = MVN <int8> v2
    (3) v4 = MOVBUreg <uint64> v3
    (3) v5 = MakeResult <uint64,mem> v4 v1
    Ret v5
name x[bool]: [v2]
"""

ARM64_SRC = """\
package main
import (
    "fmt"
    "math/bits"
    "os"
    "strconv"
)

func f0(x, y int64) int64 {
    r := x >> 33
    if bits.OnesCount8(128) > 0 { r = ^y }
    return r
}
func f1(x, y uint64) uint64 { return (x + y) ^ (x & y) }
func f2(x int64) int64 { return x >> 33 }
func f3(x, y uint64) uint64 {
    a, b := int8(x), uint16(y)
    var r int64
    if x < y { r = int64(a) } else { r = int64(b) }
    return uint64(r)
}
func b2i(b bool) uint64 { if b { return 1 }; return 0 }
func f4(x, y uint64) uint64 { return -b2i(x < y) }
func f5(x, y uint64) uint64 { return uint64(int16(b2i(uint8(^y) >= uint8(y))) + int16(-32768)) }
func f6(x, y uint64) uint64 { return b2i(uint32(b2i(uint8(x) > uint8(y))) != uint32(y)&169) }

func main() {
    x, _ := strconv.ParseInt(os.Args[1], 0, 64)
    y, _ := strconv.ParseInt(os.Args[2], 0, 64)
    fmt.Printf("%d %d %d %d %d %d %d\\n", f0(x, y), f1(uint64(x), uint64(y)), f2(x),
        f3(uint64(x), uint64(y)), f4(uint64(x), uint64(y)),
        f5(uint64(x), uint64(y)), f6(uint64(x), uint64(y)))
}
"""

# Clean Go expressions that reach shifted logical ops, flag-setting operations,
# signed bitfield insertion and both rotate widths on ARM64.
ARM64_BIT_EXPRS = []
for _shifted in ("(y << 17)", "(y >> 17)", "uint64(int64(y) >> 17)", "bits.RotateLeft64(y, -17)"):
    ARM64_BIT_EXPRS += [f"x {op} ({_shifted})" for op in ("&", "|", "^", "&^")]
    ARM64_BIT_EXPRS += [f"x {op} ^({_shifted})" for op in ("^", "|")]
    ARM64_BIT_EXPRS += [f"^({_shifted})", f"b2i(x & ({_shifted}) == 0)"]
ARM64_BIT_EXPRS += [f"b2i(x + ({s}) == 0)" for s in ("y << 17", "y >> 17", "uint64(int64(y) >> 17)")]
ARM64_BIT_EXPRS += ["uint64(int64(int8(x)) << 17)", "uint64(int32(x << 7))",
                   "bits.RotateLeft64(x, int(y))", "uint64(bits.RotateLeft32(uint32(x), int(y)))",
                   "bits.RotateLeft64(x, -17)", "uint64(bits.RotateLeft32(uint32(x), -17))",
                   "b2i(uint32(x) & uint32(y) == 0)"]


def arm64_bit_source():
    funcs = [f"//go:noinline\nfunc f{i}(x, y uint64) uint64 {{ return {expr} }}\n"
             for i, expr in enumerate(ARM64_BIT_EXPRS)]
    calls = "\n".join(f'fmt.Println(f{i}(x, y))' for i in range(len(funcs)))
    return ('''package main
import ("fmt"; "math/bits"; "os"; "strconv")
func b2i(b bool) uint64 { if b { return 1 }; return 0 }
''' + "\n".join(funcs) + '''
func main() {
    x, _ := strconv.ParseUint(os.Args[1], 0, 64)
    y, _ := strconv.ParseUint(os.Args[2], 0, 64)
''' + calls + "\n}\n")


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
class LoweredS390XModelTests(unittest.TestCase):
    def test_s390x_sign_extension_compare_bug_is_reported_at_lower(self):
        before = tv.parse_dump(S390X_PRE)
        after = tv.parse_dump(S390X_LOWER)
        rep = tv.validate([("writebarrier", S390X_PRE), ("lower", S390X_LOWER)], arch="s390x")
        self.assertEqual([f["pass"] for f in rep["failures"]], ["lower"])
        failure = rep["failures"][0]
        self.assertEqual(failure["kind"], "equivalence")
        self.assertEqual(failure["before_out"], ("ret", 0))
        self.assertEqual(failure["after_out"], ("ret", 1))
        self.assertEqual(tv.evaluate(before, {"y": 128}), ("ret", 0))
        after.arch = "s390x"
        self.assertEqual(tv.evaluate(after, {"y": 128}), ("ret", 1))

    def test_s390x_wide_compare_has_no_report(self):
        rep = tv.validate([("writebarrier", S390X_PRE), ("lower", S390X_CLEAN)], arch="s390x")
        self.assertEqual((rep["failures"], rep["unsupported"]), ([], None))

    def test_s390x_branch_condition(self):
        f = tv.parse_dump(S390X_BRANCH)
        f.arch = "s390x"
        self.assertEqual(f.block("b1").aux, "Less")
        self.assertEqual(tv.evaluate(f, {"x": 0}), ("ret", 0))
        self.assertEqual(tv.evaluate(f, {"x": M64}), ("ret", 1))


@unittest.skipUnless(HAVE_Z3, "z3 module not available")
class LoweredARM64ModelTests(unittest.TestCase):
    @staticmethod
    def _expression(body, arch=None):
        f = tv.parse_dump("""\
expression func(uint64, uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (2) v2 = ArgIntReg <uint64> {x+0} [0]
    (2) v3 = ArgIntReg <uint64> {y+0} [1]
""" + body + "\n    (4) v9 = MakeResult <uint64,mem> v8 v1\n    Ret v9\n")
        f.arch = arch
        return f

    def test_shifted_logical_ops_agree_with_generic_ssa_for_all_inputs(self):
        for shift in ("LL", "RL", "RA", "RO"):
            for count in (0, 17, 63):
                generic_shift = {"LL": "Lsh64x64", "RL": "Rsh64Ux64", "RA": "Rsh64x64",
                                 "RO": "RotateLeft64"}[shift]
                amount = (64 - count) % 64 if shift == "RO" else count
                shifted = (f"    (?) v4 = Const64 <uint64> [{amount}]\n"
                           f"    (3) v5 = {generic_shift} <uint64> v3 v4\n")
                operations = {"AND": "And64", "OR": "Or64", "XOR": "Xor64",
                              "BIC": "And64", "EON": "Xor64", "ORN": "Or64"}
                for op in (*operations, "MVN", "TST", "CMN"):
                    if op == "CMN" and shift == "RO":
                        continue
                    with self.subTest(op=op, shift=shift, count=count):
                        body = shifted
                        operand = "v5"
                        if op in ("BIC", "EON", "ORN"):
                            body += "    (3) v6 = Com64 <uint64> v5\n"
                            operand = "v6"
                        if op in ("TST", "CMN"):
                            body += (f"    (3) v6 = {'And64' if op == 'TST' else 'Add64'} <uint64> v2 v5\n"
                                     "    (?) v7 = Const64 <uint64> [0]\n"
                                     "    (3) v8 = Eq64 <bool> v6 v7")
                            machine = (f"    (3) v6 = {op}shift{shift} <flags> [{count}] v2 v3\n"
                                       "    (3) v8 = Equal <bool> v6")
                        elif op == "MVN":
                            body += "    (3) v8 = Com64 <uint64> v5"
                            machine = f"    (3) v8 = MVNshift{shift} <uint64> [{count}] v3"
                        else:
                            body += f"    (3) v8 = {operations[op]} <uint64> v2 {operand}"
                            machine = f"    (3) v8 = {op}shift{shift} <uint64> [{count}] v2 v3"
                        self.assertIsNone(tv.equivalent(self._expression(body),
                                                       self._expression(machine, "arm64")))

    def test_variable_rotates_agree_with_generic_ssa_for_all_inputs(self):
        for width in (32, 64):
            with self.subTest(width=width):
                trunc = "    (3) v4 = Trunc64to32 <uint32> v2\n" if width == 32 else ""
                src = "v4" if width == 32 else "v2"
                spec = (trunc + "    (3) v5 = Neg64 <uint64> v3\n"
                        f"    (3) v6 = RotateLeft{width} <uint{width}> {src} v5\n")
                spec += ("    (3) v8 = ZeroExt32to64 <uint64> v6" if width == 32
                         else "    (3) v8 = Copy <uint64> v6")
                machine = f"    (3) v8 = {'RORW' if width == 32 else 'ROR'} <uint64> v2 v3"
                self.assertIsNone(tv.equivalent(self._expression(spec), self._expression(machine, "arm64")))

    def test_signed_bitfield_insert_sign_extends_above_field(self):
        for aux in ("lsb=17,width=8", str((17 << 8) | 8)):
            f = self._expression(f"    (3) v8 = SBFIZ <uint64> [{aux}] v2", "arm64")
            for x in (0, 0x7F, 0x80, 0xFF, 0x123456789ABCDEF0):
                signed = (x & 0x7F) - (x & 0x80)
                self.assertEqual(tv.evaluate(f, {"x": x, "y": 0}), ("ret", (signed << 17) & M64))

    def test_word_test_flags_ignore_upper_bits(self):
        for condition, expected in (("Equal", 1), ("LessThan", 0), ("LessThanU", 1), ("GreaterEqualU", 0)):
            f = self._expression("    (3) v6 = TSTW <flags> v2 v3\n"
                                 f"    (3) v8 = {condition} <bool> v6", "arm64")
            self.assertEqual(tv.evaluate(f, {"x": 1 << 63, "y": M64}), ("ret", expected))

    def test_madd_msub_accumulator_is_first_operand(self):
        madd = tv.parse_dump(ARM64_MADD)
        msub = tv.parse_dump(ARM64_MSUB)
        madd.arch = msub.arch = "arm64"
        self.assertEqual(tv.evaluate(madd, {"x": 2, "y": 3, "z": 4}), ("ret", 14))
        self.assertEqual(tv.evaluate(msub, {"x": 2, "y": 3, "z": 4}), ("ret", M64 - 9))

    def test_mvn_converts_bool_to_integer_before_complement(self):
        f = tv.parse_dump(ARM64_MVN_BOOL)
        f.arch = "arm64"
        self.assertEqual(tv.evaluate(f, {"x": 0}), ("ret", 255))
        self.assertEqual(tv.evaluate(f, {"x": 1}), ("ret", 254))

    def test_neg_converts_condition_to_integer_before_negation(self):
        # Use an actual condition (a z3 Bool), rather than a register argument.
        text = ARM64_MVN_BOOL.replace(
            "    (3) v3 = MVN <int8> v2",
            "    (3) v6 = CMPconst <flags> [0] v2\n"
            "    (3) v7 = NotEqual <bool> v6\n"
            "    (3) v3 = NEG <int8> v7")
        f = tv.parse_dump(text)
        f.arch = "arm64"
        self.assertEqual(tv.evaluate(f, {"x": 0}), ("ret", 0))
        self.assertEqual(tv.evaluate(f, {"x": 1}), ("ret", 255))

    def test_stack_load_extensions_and_overlapping_store(self):
        template = """\
stack func(uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (?) v2 = SP <uintptr>
    (2) v3 = ArgIntReg <uint64> {x+0} [0]
    (2) v4 = MOVDaddr <*uint64> {slot} [8] v2
    (3) v5 = MOVDstore <mem> v4 v3 v1
    (3) v6 = MOVDconst <uint64> [-1]
    (3) v7 = MOVBstore <mem> [1] v4 v6 v5
    (4) v8 = LOAD <uint64> {slot} [8] v2 v7
    (4) v9 = MakeResult <uint64,mem> v8 v7
    Ret v9
"""
        x = 0xFEDCBA9876543280
        stored = (x & ~0xFF00) | 0xFF00
        for suffix, width, signed in (("B", 8, True), ("BU", 8, False),
                                      ("H", 16, True), ("HU", 16, False),
                                      ("W", 32, True), ("WU", 32, False), ("D", 64, False)):
            with self.subTest(load=suffix):
                f = tv.parse_dump(template.replace("LOAD", f"MOV{suffix}load"))
                f.arch = "arm64"
                expected = stored & ((1 << width) - 1)
                if signed and expected & (1 << (width - 1)):
                    expected -= 1 << width
                self.assertEqual(tv.evaluate(f, {"x": x}), ("ret", expected & M64))

    def test_phi_merges_condition_and_integer_register(self):
        text = """\
phiBool func(uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (2) v2 = ArgIntReg <uint64> {x+0} [0]
    (3) v3 = CMPconst <flags> [0] v2
    EQ v3 -> b2 b3
  b2: <- b1
    (4) v4 = MOVDconst <uint64> [3]
    Plain -> b4
  b3: <- b1
    (5) v5 = NotEqual <bool> v3
    Plain -> b4
  b4: <- b2 b3
    (6) v6 = Phi <uint64> v4 v5
    (6) v7 = MakeResult <uint64,mem> v6 v1
    Ret v7
"""
        f = tv.parse_dump(text)
        f.arch = "arm64"
        self.assertEqual(tv.evaluate(f, {"x": 0}), ("ret", 3))
        self.assertEqual(tv.evaluate(f, {"x": 1}), ("ret", 1))

    def test_bool_stack_store_and_unknown_base(self):
        text = """\
stackBool func(uint64) uint64
  b1:
    (?) v1 = InitMem <mem>
    (?) v2 = SP <uintptr>
    (2) v3 = ArgIntReg <uint64> {x+0} [0]
    (3) v4 = CMPconst <flags> [0] v3
    (3) v5 = NotEqual <bool> v4
    (3) v6 = MOVBstore <mem> {slot} v2 v5 v1
    (4) v7 = MOVBUload <uint64> {slot} v2 v6
    (4) v8 = MakeResult <uint64,mem> v7 v6
    Ret v8
"""
        f = tv.parse_dump(text)
        f.arch = "arm64"
        for x in (0, 1, M64):
            self.assertEqual(tv.evaluate(f, {"x": x}), ("ret", int(x != 0)))
        bad = tv.parse_dump(text.replace("{slot} v2", "{slot} v3"))
        bad.arch = "arm64"
        with self.assertRaisesRegex(tv.Unsupported, "non-stack base"):
            tv.evaluate(bad, {"x": 0})

    def test_csinv_not_miscompile_is_reported_at_lower(self):
        rep = tv.validate([("writebarrier", ARM64_PRE), ("lower", ARM64_BAD)], arch="arm64")
        self.assertEqual([f["pass"] for f in rep["failures"]], ["lower"])
        failure = rep["failures"][0]
        self.assertEqual(failure["kind"], "equivalence")
        self.assertNotEqual(failure["before_out"], failure["after_out"])
        self.assertEqual(tv.evaluate(tv.parse_dump(ARM64_PRE), {"x": 0, "y": 2}), ("ret", M64 - 2))
        bad = tv.parse_dump(ARM64_BAD)
        bad.arch = "arm64"
        self.assertEqual(tv.evaluate(bad, {"x": 0, "y": 2}), ("ret", 3))

    def test_mvn_fix_has_no_report(self):
        rep = tv.validate([("writebarrier", ARM64_PRE), ("lower", ARM64_FIXED)], arch="arm64")
        self.assertEqual((rep["failures"], rep["unsupported"]), ([], None))

    def test_signed_arm64_condition_branch(self):
        f = tv.parse_dump(ARM64_BRANCH)
        f.arch = "arm64"
        self.assertEqual(tv.evaluate(f, {"x": M64}), ("ret", 1))
        self.assertEqual(tv.evaluate(f, {"x": 1}), ("ret", 0))


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
        self.assertEqual(tv._go_string(f.values["v99"].aux), b"[\x00")
        self.assertEqual(tv.evaluate(f, {"x": 1, "y": 2}), tv.evaluate(tv.parse_dump(BUILD), {"x": 1, "y": 2}))

    def test_read_only_table_lookup(self):
        table = bytes((7 * i + 3) & 255 for i in range(256))
        lit = '"' + "".join(f"\\x{b:02x}" for b in table) + '"'
        src = BUILD.replace("    (5) v10 = Trunc64to16 <int16> v8\n", f"""\
    (5) v10 = Trunc64to16 <int16> v8
    (?) v90 = ConstString <string> {{{lit}}}
    (?) v91 = StringPtr <*uint8> v90
    (?) v92 = Trunc64to8 <uint8> v7
    (?) v93 = ZeroExt8to64 <int> v92
    (?) v94 = AddPtr <*uint8> v91 v93
    (?) v95 = Load <uint8> v94 v1
""").replace("(10) v24 = SignExt16to64 <uint64> v23", "(10) v24 = ZeroExt8to64 <uint64> v95")
        f = tv.parse_dump(src)
        f.rodata = {256: table}
        for x in (0, 5, 255, 256 + 9):
            self.assertEqual(tv.evaluate(f, {"x": x, "y": 0}), ("ret", table[x & 255]))
        opt = src.replace("(?) v91 = StringPtr <*uint8> v90", "(?) v89 = SB <uintptr>\n    (?) v91 = Addr <*uint8> {go:string..gostring.256.AbC==} v89")
        g = tv.parse_dump(opt)
        g.rodata = {256: table}
        self.assertEqual(tv.evaluate(g, {"x": 9, "y": 0}), ("ret", table[9]))
        g.rodata = {}
        with self.assertRaises(tv.Unsupported):
            tv.evaluate(g, {"x": 9, "y": 0})

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

    def test_model_error_is_reported_not_raised(self):
        bad = BUILD.replace("(5) v12 = And16 <int16> v10 v11", "(5) v12 = And16 <int16> v10")
        rep = tv.validate([("build", BUILD), ("opt", bad)])
        self.assertTrue(rep.get("model_error"))
        self.assertIn("model error", rep["unsupported"])

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
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
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


W32_SRC = """\
package main

import (
	"fmt"
	"os"
	"strconv"
)

//go:noinline
func f0(x, y uint64) uint64 { return x>>3 + y }

//go:noinline
func f1(x, y uint64) uint64 { return x - y ^ y<<7 }

//go:noinline
func f2(x, y uint64) uint64 { return x * y }

//go:noinline
func f3(x, y uint64) uint64 { return uint64(int64(x) >> (y & 63)) }

//go:noinline
func f4(x, y uint64) uint64 {
	if int64(x) < int64(y) {
		return x | 1
	}
	return y &^ x
}

//go:noinline
func f5(x, y uint64) uint64 { return uint64(int64(int32(x))) + uint64(uint32(y)) }

//go:noinline
func f6(x, y uint64) uint64 {
	if x == y {
		return 1
	}
	if x > y {
		return x - y
	}
	return y % 8
}

//go:noinline
func f7(x, y uint64) uint64 { return uint64(int8(x)/int8(y|1)) + x<<(y&63) }

func main() {
	fs := []func(uint64, uint64) uint64{f0, f1, f2, f3, f4, f5, f6, f7}
	x, _ := strconv.ParseUint(os.Args[1], 10, 64)
	y, _ := strconv.ParseUint(os.Args[2], 10, 64)
	for _, f := range fs {
		fmt.Println(f(x, y))
	}
}
"""
W32_N = 8


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class Word32Tests(unittest.TestCase):
    """Generic passes of the 32-bit little-endian targets, where dec64 splits 64-bit values."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_w32_"))
        (cls.tmp / "main.go").write_text(W32_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(W32_N)]
        cls.dumps = {a: tv.dump_passes(GO, cls.tmp, names, a) for a in ("386", "arm", "mipsle")}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_dec64_splits_arguments(self):
        last = dict(self.dumps["arm"]["f0"])["late_opt"]
        self.assertIn("Arg <uint32> {x} [4]", last)
        self.assertIn("Add32carry", last)

    def test_evaluation_matches_gc(self):
        rng = random.Random(32)
        pts = [(0, 0), (M64, M64), (0xFFFFFFFF, 1), (1 << 63, 33), (1 << 32, 0xFFFFFFFF), (5, 31)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(4)]
        for x, y in pts:
            out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                                 text=True, check=True).stdout.split()
            for arch, dumps in self.dumps.items():
                for i in range(W32_N):
                    for name, dump in (dumps[f"f{i}"][0], dumps[f"f{i}"][-1]):
                        f = tv.parse_dump(dump)
                        f.word_bits = 32
                        got = tv.evaluate(f, {"x": x, "y": y})
                        self.assertEqual(got, ("ret", int(out[i])), (arch, f"f{i}", name, x, y))

    def test_validate_reports_no_failure(self):
        for arch, dumps in self.dumps.items():
            for i in range(W32_N):
                rep = tv.validate(dumps[f"f{i}"], 32)
                self.assertEqual(rep["failures"], [], (arch, f"f{i}"))
                self.assertIsNone(rep["unsupported"], (arch, f"f{i}"))
                self.assertGreater(rep["checked"], 0, (arch, f"f{i}"))

    def test_wrong_carry_is_reported(self):
        passes = self.dumps["arm"]["f0"]
        i = next(k for k, (n, t) in enumerate(passes) if "Add32withcarry" in t)
        bad = [(n, t.replace("Add32withcarry", "Sub32withcarry") if k >= i else t) for k, (n, t) in enumerate(passes)]
        rep = tv.validate(bad, 32)
        self.assertEqual([r["kind"] for r in rep["failures"]], ["equivalence"])


ARM_SRC = """\
package main

import (
	"fmt"
	"math/bits"
	"os"
	"strconv"
)

//go:noinline
func f0(x, y uint64) uint64 { return uint64(uint32(x) << (y & 63)) }

//go:noinline
func f1(x, y uint64) uint64 { return uint64(int32(x) >> uint8(y)) }

//go:noinline
func f2(x, y uint64) uint64 { return uint64(uint32(x)/(uint32(y)|1)) + uint64(uint32(x)%(uint32(y)|1)) }

//go:noinline
func f3(x, y uint64) uint64 {
	return uint64(bits.LeadingZeros32(uint32(x))) + uint64(bits.ReverseBytes32(uint32(y)))
}

//go:noinline
func f4(x, y uint64) uint64 { return uint64(int8(x>>3)) - uint64(uint16(y)>>2) ^ uint64(^(int32(y) >> 5)) }

//go:noinline
func f5(x, y uint64) uint64 {
	if int32(x) < int32(y) {
		return 7
	}
	if uint32(x) >= uint32(y) {
		return 9
	}
	return 3
}

//go:noinline
func f6(x, y uint64) uint64 { return uint64(int32(x)*int32(y)) + uint64(uint32(x)>>uint32(y)) }

// Register-shift operands: ORshiftLLreg, CMPshiftLLreg (three arguments, no flags).
//
//go:noinline
func f7(x, y uint64) uint64 {
	r := uint64(int64(9223372036854775806) ^ int64(x)>>uint8(y))
	if uint32(2147483648)<<uint8(y) <= uint32(x) {
		r ^= 1
	}
	return r
}

// golang/go#82786: the MVNshiftRA constant fold computes ^(c>>d) with a logical shift.
//
//go:noinline
func f8(x, y uint64) uint64 {
	return uint64(bits.TrailingZeros64(uint64(uint16(bits.OnesCount16(16384))) &^ 16777217))
}

func main() {
	fs := []func(uint64, uint64) uint64{f0, f1, f2, f3, f4, f5, f6, f7, f8}
	x, _ := strconv.ParseUint(os.Args[1], 10, 64)
	y, _ := strconv.ParseUint(os.Args[2], 10, 64)
	for _, f := range fs {
		fmt.Println(f(x, y))
	}
}
"""
ARM_N = 9  # f8 is golang/go#82786


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredARMTests(unittest.TestCase):
    """Lowered 32-bit arm passes, optimized and -N, against the native program."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_arm_"))
        (cls.tmp / "main.go").write_text(ARM_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(ARM_N)]
        cls.dumps = {fl: tv.dump_passes(GO, cls.tmp, names, "arm", lowered=True, gcflags=fl)
                     for fl in ("", "-N -l")}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_lowered_evaluation_matches_gc(self):
        rng = random.Random(7)
        pts = [(0, 0), (M64, M64), (0x80000000, 31), (0x80000000, 32), (0xFFFF8000, 255), (65536, 256),
               (5, 0xFFFFFFFF), (0x7FFFFFFF, 0x80000000), (3, 2)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(4)]
        for x, y in pts:
            out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                                 text=True, check=True).stdout.split()
            for fl, dumps in self.dumps.items():
                for i in range(ARM_N - 1):
                    if fl and i == 3:
                        continue  # a math/bits helper left as a call by -l
                    for name in ("lower", "flagalloc"):
                        f = tv.parse_dump(dict(dumps[f"f{i}"])[name])
                        f.arch, f.word_bits, f.param_names = "arm", 32, {"x", "y"}
                        got = tv.evaluate(f, {"x": x, "y": y})
                        self.assertEqual(got, ("ret", int(out[i])), (fl, f"f{i}", name, x, y))

    def test_finds_82786(self):
        rep = tv.validate(self.dumps[""]["f8"], 32, arch="arm")
        eq = [r for r in rep["failures"] if r["kind"] == "equivalence"]
        self.assertEqual([r["pass"] for r in eq], ["lower"])
        self.assertEqual(eq[0]["before_out"], ("ret", 64))

    def test_no_report_on_correct_functions(self):
        for fl, dumps in self.dumps.items():
            for i in range(ARM_N - 1):
                rep = tv.validate(dumps[f"f{i}"], 32, arch="arm")
                self.assertEqual(rep["failures"], [], (fl, f"f{i}"))
                if not (fl and i == 3):
                    self.assertIsNone(rep["unsupported"], (fl, f"f{i}"))

    def test_noov_conditions_read_n_alone(self):
        ctx = z3.Context()
        t, f = z3.BoolVal(True, ctx), z3.BoolVal(False, ctx)
        flags = ("arm64flags", t, f, f, t)  # N=1, V=1: MI is taken, LT is not
        self.assertTrue(z3.is_true(z3.simplify(tv._arm64_condition("LessThanNoov", flags))))
        self.assertTrue(z3.is_false(z3.simplify(tv._arm64_condition("LessThan", flags))))
        self.assertTrue(z3.is_false(z3.simplify(tv._arm64_condition("GreaterEqualNoov", flags))))


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


PPC_CALLS_N = (3, 9)  # math/bits helpers stay calls with -l


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredPPC64Tests(unittest.TestCase):
    """Lowered ppc64 passes: machine semantics against the native (amd64) program."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_ppc_"))
        (cls.tmp / "main.go").write_text(PPC_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(11)]
        cls.dumps = {}
        for cpu, fl in (("power8", ""), ("power9", ""), ("power10", ""), ("power8", "-N -l")):
            os.environ["GOPPC64"] = cpu
            try:
                cls.dumps[cpu + fl] = tv.dump_passes(GO, cls.tmp, names, "ppc64le", lowered=True, gcflags=fl)
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
                        try:
                            got = tv.evaluate(f, {"x": x, "y": y})
                        except tv.Unsupported:
                            if cpu.endswith("-l") and i in PPC_CALLS_N:
                                continue  # a math/bits helper left as a call by -l
                            raise
                        self.assertEqual(got, ("ret", int(out[i])), (cpu, f"f{i}", name, x, y))

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
                if cpu.endswith("-l") and i in PPC_CALLS_N:  # may be a call: unsupported, never a failure
                    self.assertEqual(rep["failures"], [], (cpu, f"f{i}"))
                    continue
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
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
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


RV_SRC = AMD_SRC.replace("func main() {", """//go:noinline
func f13(x, y uint64) uint64 { a := int8(x); return uint64((a - (-a)) >> 8) }

func main() {""").replace("f11, f12}", "f11, f12, f13}")
RV_N = 14
RV_TABLES = (3, 9)  # bits.Len64/TrailingZeros64 read a global table without Zbb (unsupported)


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredRISCV64Tests(unittest.TestCase):
    """Lowered riscv64 passes, optimized and -N, against the native program."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_rv_"))
        (cls.tmp / "main.go").write_text(RV_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(RV_N)]
        cls.dumps = {fl: tv.dump_passes(GO, cls.tmp, names, "riscv64", lowered=True, gcflags=fl)
                     for fl in ("", "-N -l")}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_lowered_evaluation_matches_gc(self):
        rng = random.Random(11)
        pts = [(1, 0), (M64, M64), (1 << 31, 0), (0x80000000, 1), (0xFFFF8000, 31), (65536, 7),
               (1 << 63, M64), (0x80000000, 0xFFFFFFFF), (1 << 63 | 5, 3), (3, 2)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(4)]
        for x, y in pts:
            out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                                 text=True, check=True).stdout.split()
            for fl, dumps in self.dumps.items():
                for i in range(RV_N - 1):  # f13 is miscompiled on riscv64 (golang/go#82773)
                    if i in RV_TABLES:
                        continue
                    for name in ("lower", "flagalloc"):
                        f = tv.parse_dump(dict(dumps[f"f{i}"])[name])
                        f.arch = "riscv64"
                        self.assertEqual(tv.evaluate(f, {"x": x, "y": y}), ("ret", int(out[i])),
                                         (fl, f"f{i}", name, x, y))

    def test_finds_82773(self):
        for fl, dumps in self.dumps.items():
            rep = tv.validate(dumps["f13"], arch="riscv64")
            eq = [r for r in rep["failures"] if r["kind"] == "equivalence"]
            self.assertEqual([r["pass"] for r in eq], ["lower"], fl)
            x = eq[0]["inputs"]["x"] & 0xFF
            a = x - 256 if x >> 7 else x
            r = ((a + a + 128) % 256) - 128  # int8(a - (-a))
            self.assertEqual(eq[0]["before_out"], ("ret", (r >> 8) & M64))
            self.assertNotEqual(eq[0]["after_out"], eq[0]["before_out"])

    def test_no_report_on_correct_functions(self):
        for fl, dumps in self.dumps.items():
            for i in range(RV_N - 1):
                rep = tv.validate(dumps[f"f{i}"], arch="riscv64")
                if i in RV_TABLES:  # reported as unsupported, never as a failure
                    self.assertEqual(rep["failures"], [], (fl, f"f{i}"))
                    self.assertIsNotNone(rep["unsupported"], (fl, f"f{i}"))
                    continue
                self.assertEqual((rep["failures"], rep["unsupported"]), ([], None), (fl, f"f{i}"))


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredLOONG64Tests(unittest.TestCase):
    """Lowered loong64 passes, optimized and -N, against the native program."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_la_"))
        (cls.tmp / "main.go").write_text(RV_SRC)
        (cls.tmp / "go.mod").write_text("module m\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(RV_N)]
        cls.dumps = {fl: tv.dump_passes(GO, cls.tmp, names, "loong64", lowered=True, gcflags=fl)
                     for fl in ("", "-N -l")}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def test_lowered_evaluation_matches_gc(self):
        rng = random.Random(13)
        pts = [(1, 0), (M64, M64), (1 << 31, 0), (0x80000000, 1), (0xFFFF8000, 31), (65536, 7),
               (1 << 63, M64), (0x80000000, 0xFFFFFFFF), (1 << 63 | 5, 3), (3, 2)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(4)]
        for x, y in pts:
            out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                                 text=True, check=True).stdout.split()
            for fl, dumps in self.dumps.items():
                for i in range(RV_N - 1):  # f13: golang/go#82773, still open on loong64
                    for name in ("lower", "flagalloc"):
                        f = tv.parse_dump(dict(dumps[f"f{i}"])[name])
                        f.arch = "loong64"
                        try:
                            got = tv.evaluate(f, {"x": x, "y": y})
                        except tv.Unsupported:
                            if fl and i in (3, 9):
                                continue  # a math/bits helper left as a call by -l
                            raise
                        self.assertEqual(got, ("ret", int(out[i])), (fl, f"f{i}", name, x, y))

    def test_finds_82773(self):
        for fl, dumps in self.dumps.items():
            rep = tv.validate(dumps["f13"], arch="loong64")
            eq = [r for r in rep["failures"] if r["kind"] == "equivalence"]
            self.assertEqual([r["pass"] for r in eq], ["lower"], fl)

    def test_no_report_on_correct_functions(self):
        for fl, dumps in self.dumps.items():
            for i in range(RV_N - 1):
                rep = tv.validate(dumps[f"f{i}"], arch="loong64")
                self.assertEqual(rep["failures"], [], (fl, f"f{i}"))
                if not (fl and i in (3, 9)):
                    self.assertIsNone(rep["unsupported"], (fl, f"f{i}"))


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredS390XTests(unittest.TestCase):
    """Lowered s390x operations, compared with the same Go functions on native amd64."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_s390x_"))
        (cls.tmp / "main.go").write_text(S390X_SRC)
        (cls.tmp / "go.mod").write_text("module s390test\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
        names = [f"f{i}" for i in range(4)]
        # The s390x model currently covers optimized register SSA. Debug builds
        # retain stack MOVDstore operations that are not modelled here.
        cls.dumps = {"": tv.dump_passes(GO, cls.tmp, names, "s390x", lowered=True)}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def _native(self, x, y):
        out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                             text=True, check=True).stdout.split()
        return [int(v) for v in out]

    def test_native_evaluation_matches_s390x_model_on_clean_functions(self):
        rng = random.Random(17)
        pts = [(0, 0), (M64, M64), (1 << 63, 0x80), (0x7FFFFFFF, 0xFFFFFFF0)]
        pts += [(rng.getrandbits(64), rng.getrandbits(64)) for _ in range(5)]
        for x, y in pts:
            out = self._native(x, y)
            for fl, dumps in self.dumps.items():
                for i in (2, 3):
                    for name in ("lower", "flagalloc"):
                        f = tv.parse_dump(dict(dumps[f"f{i}"])[name])
                        f.arch = "s390x"
                        self.assertEqual(tv.evaluate(f, {"x": x, "y": y}), ("ret", out[i]),
                                         (fl, f"f{i}", name, x, y))

    def test_known_bug_site_or_fixed_toolchain(self):
        version = subprocess.run([GO, "version"], capture_output=True, text=True, check=True).stdout
        for fl, dumps in self.dumps.items():
            for i in (0, 1):
                rep = tv.validate(dumps[f"f{i}"], arch="s390x")
                if any(v in version for v in ("go1.26", "go1.27", "56ae71df05")):
                    eq = [f for f in rep["failures"] if f["kind"] == "equivalence"]
                    self.assertEqual([f["pass"] for f in eq], ["lower"], (version, fl, f"f{i}"))
                else:
                    self.assertEqual((rep["failures"], rep["unsupported"]), ([], None),
                                     (version, fl, f"f{i}"))

    def test_no_report_on_correct_functions(self):
        for fl, dumps in self.dumps.items():
            for i in (2, 3):
                rep = tv.validate(dumps[f"f{i}"], arch="s390x")
                self.assertEqual((rep["failures"], rep["unsupported"]), ([], None), (fl, f"f{i}"))


@unittest.skipUnless(HAVE_Z3 and GO, "z3 module or go not available")
class LoweredARM64Tests(unittest.TestCase):
    """Lowered arm64 operations, compared with the same Go functions on native amd64."""

    @classmethod
    def setUpClass(cls):
        cls.tmp = Path(tempfile.mkdtemp(prefix="ssa_tv_arm64_"))
        (cls.tmp / "main.go").write_text(ARM64_SRC)
        (cls.tmp / "go.mod").write_text("module arm64test\n\ngo 1.22\n")
        subprocess.run([GO, "build", "-buildvcs=false", "-o", "prog", "."], cwd=cls.tmp, check=True)
        cls.dumps = {fl: tv.dump_passes(GO, cls.tmp, [f"f{i}" for i in range(7)], "arm64",
                                      lowered=True, gcflags=fl) for fl in ("", "-N -l")}

    @classmethod
    def tearDownClass(cls):
        shutil.rmtree(cls.tmp, ignore_errors=True)

    def _native(self, x, y):
        out = subprocess.run([str(self.tmp / "prog"), str(x), str(y)], capture_output=True,
                             text=True, check=True).stdout.split()
        return [int(v) for v in out]

    def test_native_evaluation_matches_arm64_model_on_clean_functions(self):
        rng = random.Random(23)
        pts = [(0, 0), (-1, 2), (-(1 << 63), -1), ((1 << 62) - 1, -(1 << 62))]
        pts += [(rng.randint(-(1 << 63), (1 << 63) - 1), rng.randint(-(1 << 63), (1 << 63) - 1))
                for _ in range(5)]
        for x, y in pts:
            out = self._native(x, y)
            for fl, dumps in self.dumps.items():
                for i in range(1, 7):
                    for stage in ("lower", "flagalloc"):
                        f = tv.parse_dump(dict(dumps[f"f{i}"])[stage])
                        f.arch = "arm64"
                        self.assertEqual(tv.evaluate(f, {"x": x, "y": y}), ("ret", out[i] & M64),
                                         (fl, f"f{i}", stage, x, y))

    def test_known_bug_site_or_fixed_toolchain(self):
        version = subprocess.run([GO, "version"], capture_output=True, text=True, check=True).stdout
        lower = dict(self.dumps[""]["f0"])["lower"]
        rep = tv.validate([("writebarrier", ARM64_PRE), ("lower", lower)], arch="arm64")
        model = tv.parse_dump(lower)
        model.arch = "arm64"
        value = tv.evaluate(model, {"x": 0, "y": 2})
        native = self._native(0, 2)[0]
        if "go1.27" in version or "56ae71df05" in version:
            eq = [f for f in rep["failures"] if f["kind"] == "equivalence"]
            self.assertEqual([f["pass"] for f in eq], ["lower"], (version, rep))
            self.assertEqual((value, native & M64), (("ret", 3), M64 - 2), version)
        else:
            self.assertEqual((rep["failures"], rep["unsupported"]), ([], None), (version, rep))
            self.assertEqual(value, ("ret", native & M64), (version, value, native))

    def test_no_report_on_correct_functions(self):
        for fl, dumps in self.dumps.items():
            for i in range(1, 7):
                rep = tv.validate(dumps[f"f{i}"], arch="arm64")
                self.assertEqual((rep["failures"], rep["unsupported"]), ([], None), (fl, f"f{i}"))


if __name__ == "__main__":
    unittest.main()
