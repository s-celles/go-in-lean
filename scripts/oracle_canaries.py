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

CANARIES = [
    {"id": "82763", "expect": ("go1.27.3:CAUGHT", "tip:CAUGHT"),
     "tree": C82763, "inputs": [((1 << 64) - 1, 0), (7, 3)]},
    {"id": "82767", "expect": ("go1.27.3:CLEAN", "tip:CAUGHT"),
     "tree": C82767, "inputs": [(2, 0), ((1 << 64) - 5, 0)]},
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
        if n["k"] == "lit":
            lits.append(n)
        for k in ("a", "b"):
            if k in n:
                collect(n[k])
    collect(tree)
    cn, decls = {}, ""
    for j, n in enumerate(lits):
        cn[id(n)] = f"c{j}"
        decls += f"\tvar c{j} = {ob.GONAME[n['t']]}({ob.signed_repr(n['t'], n['v'])})\n"
    src = ob.GOHEADER + ("\n//go:noinline\nfunc v0(x, y uint64) (res uint64, pn string) {\n"
                         "\tdefer func() { if e := recover(); e != nil { pn = panicName(e) } }()\n"
                         f"{decls}"
                         f"\tres = uint64({g.go(tree, cn)})\n\treturn\n}}\n\nfunc main() {{\n")
    src += "\tvar r uint64\n\tvar p string\n"
    for (x, y) in inputs:
        src += (f"\tr, p = v0({x}, {y})\n"
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
    lake = os.environ.get("LAKE", "lake")
    lean = subprocess.run([lake, "exe", "oracle", os.path.abspath(os.path.join(out, "exprs.json"))],
                          capture_output=True, text=True, timeout=300)
    if lean.returncode != 0:
        return None, f"oracle failed: {lean.stderr[:200]}"
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
