#!/usr/bin/env python3
"""Directed canary suite for the Lean oracle (milestone J2).

Runs a fixed list of known-bug shapes (the ones expressible in the
oracle_bits.py grammar) through the full oracle pipeline - RPN records to
`lake exe oracle`, the equivalent Go program to the toolchain under test,
line-by-line comparison - and reports, per canary and per toolchain, whether
the oracle catches the known miscompilation.

The expectations double as a merge monitor: a canary flips from CAUGHT to
CLEAN exactly when the upstream fix reaches the toolchain (CL 857741 for
golang/go#82763, CL 857342 for golang/go#82767).

Usage: oracle_canaries.py [TOOLCHAIN_BIN ...]   (default: "go" and the
GoInLean go-tip if present at ~/git/golang/go-tip/bin/go)
"""
import json, os, subprocess, sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import oracle_bits as ob

LIT = lambda w, s, v: {"k": "lit", "t": (w, s), "v": v % (1 << w)}
VAR = lambda w, s, which: {"k": "var", "t": (w, s), "which": which}


def BIN(op, a, b):
    return {"k": "bin", "op": op, "a": a, "b": b}


# golang/go#82763: ((x >> (1<<63)) & 3) << 1, x = -1: spec 6, buggy 0.
# Wrong on go1.25..1.27 and master until CL 857741 merges.
C82763 = BIN("shl",
             BIN("and",
                 BIN("shr", VAR(64, True, "x"), LIT(64, False, 1 << 63)),
                 LIT(64, True, 3)),
             LIT(64, False, 1))

# golang/go#82767: (y >> 1) >> (1<<62) for int32 y: spec 0 / -1, tip gives
# 1 / -3. Master-only regression until CL 857342 merges.
C82767 = BIN("shr",
             BIN("shr", VAR(32, True, "x"), LIT(32, True, 1)),
             LIT(64, False, 1 << 62))

# golang/go#82772 (mips/mipsle): (x*k) >> s sign-extends from bit 15; spec -1, buggy -8.
C82772 = BIN("shr", BIN("mul", VAR(8, True, "x"), LIT(8, True, -15)),
            VAR(64, False, "y"))
# golang/go#82776 (mips/mipsle): (x >> 7) >> (uint64(y) | 0xFFFFFFFF) == 1; spec 0.
C82776 = BIN("shr", BIN("shr", VAR(8, True, "x"), LIT(8, True, 7)),
            BIN("or", VAR(64, False, "y"), LIT(64, False, (1 << 32) - 1)))
# golang/go#82775 (ppc64/ppc64le): int32(int16(x >> 1)) keeps 32 bits; spec 0.
C82775 = {"k": "conv", "t": (32, True),
          "a": {"k": "conv", "t": (16, True),
                "a": BIN("shr", VAR(32, True, "x"), LIT(32, True, 1))}}
# golang/go#82773 (riscv64): (x - (-x)) >> 8 compiles to 0; spec -1.
C82773 = BIN("shr", BIN("sub", VAR(8, True, "x"),
                         {"k": "un", "op": "neg", "a": VAR(8, True, "x")}),
             LIT(64, False, 8))
# golang/go#82786 (arm): TrailingZeros64(x &^ 16777217) with x==0 gives 32; spec 64.
C82786 = {"k": "bits", "op": "tz", "w": 64,
          "a": BIN("andnot",
                   {"k": "conv", "t": (64, False),
                    "a": {"k": "conv", "t": (16, False),
                          "a": {"k": "bits", "op": "oc", "w": 16,
                                "a": LIT(16, False, 16384)}}},
                   LIT(64, False, 16777217))}

# golang/go#82774 (s390x): uint64(int8(-128)) < 0xFFFFFFFF is true; spec false.
C82774 = BIN("lt",
             {"k": "conv", "t": (64, False),
              "a": {"k": "conv", "t": (8, True), "a": VAR(8, True, "x")}},
             {"k": "lit", "t": (64, False), "v": 0xFFFFFFFF, "raw": True})

# golang/go#82777 (arm64): a constant-condition select of ^y returns y^1.
C82777 = {"k": "sel", "t": (64, True),
          "c": BIN("gt", {"k": "bits", "op": "oc", "w": 8,
                          "a": {"k": "lit", "t": (8, False), "v": 128, "raw": True}},
                   {"k": "lit", "t": (64, True), "v": 0, "raw": True}),
          "a": {"k": "un", "op": "com", "a": VAR(64, True, "y")},
          "b": BIN("shr", VAR(64, True, "x"), LIT(64, False, 33))}
# golang/go#82782 (ppc64le power10): the select picks the taken-arm value
# although y <= z is false; ^ReverseBytes16(k) should survive.
C82782 = {"k": "sel", "t": (16, True),
          "c": BIN("le", VAR(16, True, "y"), {"k": "lit", "t": (16, True), "v": 1, "raw": True}),
          "a": {"k": "lit", "t": (16, True), "v": 7, "raw": True},
          "b": {"k": "un", "op": "com",
                "a": {"k": "conv", "t": (16, True),
                      "a": {"k": "bits", "op": "rb", "w": 16,
                            "a": {"k": "conv", "t": (16, False), "a": VAR(16, False, "x")}}}}}

# golang/go#82834 (arm): bits.Sub64's borrow extraction drops a term; f(-1,1)
# answers 0 instead of 1. Also the GOARM=5 manifestation of #82786.
C82834 = {"k": "conv", "t": (16, True),
          "a": {"k": "sub64", "o": "borrow",
                "a": {"k": "conv", "t": (64, False),
                      "a": {"k": "bin", "op": "div",
                            "a": {"k": "conv", "t": (8, True),
                                  "a": {"k": "bits", "op": "rev", "w": 8,
                                        "a": {"k": "lit", "t": (8, False), "v": 33, "raw": True}}},
                            "b": {"k": "lit", "t": (8, True), "v": -7, "raw": True}}},
                "b": {"k": "conv", "t": (64, False), "a": VAR(16, True, "x")},
                "c": {"k": "conv", "t": (64, False),
                      "a": {"k": "conv", "t": (8, False), "a": VAR(8, False, "y")}}}}

# golang/go#82825 (amd64/386): the comparison of the shift count against the
# width shares the CMP flags with the SBB carry mask; y == 64 reads them
# clobbered. f(1, 65): spec 0, buggy 1.
C82825 = BIN("add",
             BIN("shl", VAR(64, False, "x"), VAR(64, False, "y")),
             {"k": "conv", "t": (64, False),
              "a": BIN("eq", VAR(64, False, "y"),
                       {"k": "lit", "t": (64, False), "v": 64, "raw": True})})
# golang/go#82839 (amd64, go1.26+): prove truncates the wide comparison
# constant when carrying the fact through the sign extension, and the
# always-false branch is folded to taken. Bisected to the minimal shape from
# the bce3 seed 783785: int64(int16(int(uint8(y))) - 257) < -131073, whose
# body sets the result; the spec keeps 0, the miscompiling toolchain sets it.
C82839 = {"k": "sel", "t": (64, True),
          "c": BIN("lt",
                   {"k": "conv", "t": (64, True),
                    "a": BIN("sub",
                             {"k": "conv", "t": (16, True),
                              "a": {"k": "conv", "t": (64, True),
                                    "a": {"k": "conv", "t": (8, False),
                                          "a": VAR(64, False, "y")}}},
                             {"k": "lit", "t": (16, True), "v": 257, "raw": True, "untyped": True})},
                   {"k": "lit", "t": (64, True), "v": -131073, "raw": True, "untyped": True}),
          "a": {"k": "lit", "t": (64, True), "v": 12345, "raw": True},
          "b": {"k": "lit", "t": (64, True), "v": 0, "raw": True}}

CANARIES = [
    {"id": "82763", "expect": ("go1.27.3:CAUGHT", "tip:CAUGHT"),
     "tree": C82763, "inputs": [((1 << 64) - 1, 0), (7, 3)]},
    {"id": "82767", "expect": ("go1.27.3:CLEAN", "tip:CAUGHT"),
     "tree": C82767, "inputs": [(2, 0), ((1 << 64) - 5, 0)]},
    {"id": "82772", "expect": ("mipsle:CAUGHT",), "arch": ("mipsle", "qemu-mipsel"),
     "tree": C82772, "inputs": [(127, 8), (127, 3)]},
    {"id": "82776", "expect": ("mipsle:CAUGHT",), "arch": ("mipsle", "qemu-mipsel"),
     "tree": C82776, "inputs": [(127, (1 << 64) - 128)]},
    {"id": "82775", "expect": ("ppc64le:CAUGHT",), "arch": ("ppc64le", "qemu-ppc64le"),
     "tree": C82775, "inputs": [((1 << 64) - (1 << 31), 0)]},
    {"id": "82773", "expect": ("riscv64:CAUGHT",), "arch": ("riscv64", "qemu-riscv64"),
     "tree": C82773, "inputs": [((1 << 64) - 1, 0)]},
    {"id": "82786", "expect": ("arm:CAUGHT",), "arch": ("arm", "qemu-arm", "GOARM=7"),
     "tree": C82786, "inputs": [(0, 0)]},
    {"id": "82774", "expect": ("s390x:CAUGHT",), "arch": ("s390x", "qemu-s390x"),
     "tree": C82774, "inputs": [(128, 0)]},
    {"id": "82777", "expect": ("arm64:CAUGHT",), "arch": ("arm64", "qemu-aarch64"),
     "tree": C82777, "inputs": [(0, 2)]},
    {"id": "82782", "expect": ("ppc64le-power10:CAUGHT",),
     "arch": ("ppc64le", "qemu-ppc64le", "GOPPC64=power10", "QEMU_CPU=power10"),
     "tree": C82782, "inputs": [(1024, 5)]},
    {"id": "82834", "expect": ("arm5:CAUGHT",), "arch": ("arm", "qemu-arm", "GOARM=5"),
     "tree": C82834, "inputs": [((1 << 64) - 1, 1)]},
    {"id": "82825", "expect": ("go1.24..master:CAUGHT",),
     "tree": C82825, "inputs": [(1, 65), (1, 64)]},
    {"id": "82839", "expect": ("go1.26+:CAUGHT",),
     "tree": C82839, "inputs": [(0, 0), (7, 255)]},
]


def run_canary(tree, inputs, gobin, out):
    os.makedirs(os.path.join(out, "gomain"), exist_ok=True)
    g = ob.Gen(None)
    recs = []
    for (x, y) in inputs:
        ops = []
        g.rpn(tree, x, y, ops)
        recs.append({"e": 0, "x": x, "y": y, "ops": ops})
    open(os.path.join(out, "exprs.json"), "w").write(json.dumps(recs))
    lits = []

    def collect(n):
        if n["k"] == "lit" and not n.get("raw"):
            lits.append(n)
        for k in ("a", "b", "c"):
            if k in n:
                collect(n[k])
    collect(tree)
    cn, decls = {}, ""
    for j, n in enumerate(lits):
        cn[id(n)] = f"c{j}"
        decls += f"\tvar c{j} = {ob.GONAME[n['t']]}({ob.signed_repr(n['t'], n['v'])})\n"
    if tree["k"] == "sel":
        T = ob.GONAME[tree["t"]]

        def emit_sel(n, indent):
            # r = <else>; if <c> { [nested sel | r = <then>] }
            inner = (indent + "r = " + g.go(n["b"], cn) + "\n" +
                     indent + "if " + g.go(n["c"], cn) + " {\n")
            if n["a"]["k"] == "sel" and n["a"].get("t") == n["t"]:
                inner += emit_sel(n["a"], indent + "\t") + "\n"
            else:
                inner += indent + "\tr = " + g.go(n["a"], cn) + "\n"
            return inner + indent + "}"

        body = ("var r " + T + "\n" + emit_sel(tree, "\t") + "\n"
                "\tres = uint64(r)")
    else:
        body = g.go(tree, cn)
        if tree["k"] == "bin" and tree["op"] in ("lt", "le", "gt", "ge", "eq", "ne"):
            body = f"b2i({body})"
    tail = body + "\n" if tree["k"] == "sel" else f"\tres = uint64({body})\n"
    src = ob.GOHEADER + ("\n//go:noinline\nfunc v0(x, y uint64) (res uint64, pn string) {\n"
                         "\tdefer func() { if e := recover(); e != nil { pn = panicName(e) } }()\n"
                         f"{decls}"
                         f"{tail}"
                         "\treturn\n}\n\nfunc main() {\n")
    src += "\tvar r uint64\n\tvar p string\n"
    # inputs travel through a package-level var: literal arguments or a local
    # literal array would be constant-propagated and the branch evaluated
    # (correctly) at compile time
    tail_idx = src.rindex("func main() {")
    flat = ", ".join(str(v) for pair in inputs for v in pair)
    src = (src[:tail_idx] +
           "var gin = [" + str(2 * len(inputs)) + "]uint64{" + flat + "}\n\n" +
           src[tail_idx:])
    # the input array is FILLED AT RUNTIME: a composite literal (even a
    # package-level one) stays constant-foldable, and a folded argument makes
    # the branch evaluate (correctly) at compile time
    src += ("\tvar gcan [" + str(len(inputs)) + "][2]uint64\n"
            "\tk := 0\n"
            "\tfor i := 0; i < " + str(2 * len(inputs)) + "; i += 2 {\n"
            "\t\tgcan[k][0] = gin[i]\n\t\tgcan[k][1] = gin[i+1]\n\t\tk++\n\t}\n")
    for i, (x, y) in enumerate(inputs):
        src += (f"\tr, p = v0(gcan[{i}][0], gcan[{i}][1])\n"
                f"\tif p == \"\" {{\n\t\tfmt.Printf(\"e=0 x={x} y={y} OK %d\\n\", r)\n"
                f"\t}} else {{\n\t\tfmt.Printf(\"e=0 x={x} y={y} PANIC %s\\n\", p)\n\t}}\n")
    src += "}\n"
    open(os.path.join(out, "gomain", "main.go"), "w").write(src)
    open(os.path.join(out, "gomain", "go.mod"), "w").write("module canary\ngo 1.25\n")
    env = dict(os.environ, GOTOOLCHAIN=os.environ.get("GOTOOLCHAIN", "local"))
    go = subprocess.run([gobin, "run", "."], cwd=os.path.join(out, "gomain"),
                        capture_output=True, text=True, env=env, timeout=300)
    if go.returncode != 0:
        return None, f"build failed: {go.stderr[:200]}"
    obin = os.environ.get("ORACLE_BIN")
    exprs = os.path.abspath(os.path.join(out, "exprs.json"))
    if obin:
        lean = subprocess.run([obin, exprs], capture_output=True, text=True, timeout=300)
    else:
        lake = os.environ.get("LAKE", "lake")
        lean = subprocess.run([lake, "exe", "oracle", exprs],
                              capture_output=True, text=True, timeout=300)
    if lean.returncode != 0:
        return None, f"oracle failed: {lean.stderr[:200]}"
    open(os.path.join(out, "expected.txt"), "w").write(lean.stdout)
    if os.environ.get("ORACLE_EMIT_ONLY"):
        return [], None
    diffs = [(a, b) for a, b in zip(go.stdout.splitlines(), lean.stdout.splitlines()) if a != b]
    return diffs, None


def main():
    tips = ["go"]
    tip = os.path.expanduser("~/git/golang/go-tip/bin/go")
    if os.path.exists(tip):
        tips.append(tip)
    tips += sys.argv[1:]
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    for c in CANARIES:
        print(f"canary #{c['id']}  (expected: {' '.join(c['expect'])})")
        if "arch" in c:
            arch, emu, *extra = c["arch"]
            out = f"/tmp/oracle-canary-{c['id']}-{arch}"
            os.environ["ORACLE_EMIT_ONLY"] = "1"
            run_canary(c["tree"], c["inputs"], tips[0], out)
            del os.environ["ORACLE_EMIT_ONLY"]
            env = " ".join(extra) + " " if extra else ""
            print(f"  emitted {out} -> remote: oracle_cross_remote.sh {out} {arch} {emu} {env}".rstrip())
            continue
        for gobin in tips:
            name = "tip" if "go-tip" in gobin else subprocess.run(
                [gobin, "version"], capture_output=True, text=True).stdout.split()[2]
            out = f"/tmp/oracle-canary-{c['id']}-{os.path.basename(os.path.dirname(os.path.dirname(gobin)))}"
            diffs, err = run_canary(c["tree"], c["inputs"], gobin, out)
            if err:
                print(f"  {name:12}: ERROR {err}")
            elif diffs:
                print(f"  {name:12}: CAUGHT ({len(diffs)} divergences)")
                for a, b in diffs[:2]:
                    print(f"    go  : {a}")
                    print(f"    lean: {b}")
            else:
                print(f"  {name:12}: CLEAN (toolchain agrees with the spec)")


if __name__ == "__main__":
    main()
