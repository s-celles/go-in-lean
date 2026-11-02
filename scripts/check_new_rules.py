#!/usr/bin/env python3
"""Translate and check only the generic.rules instances that are new on a newer GOROOT.

Usage: check_new_rules.py OLD_GOROOT NEW_GOROOT
Writes build/NewRules.lean, runs Lean on it and prints a triage (proved / counterexample /
timeout / spurious / elab_error / untranslated) for the added rules.
"""
import collections, os, re, subprocess, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import generic_rules_to_lean as g
from arm64_shift_rules import expand
from rules_diff import norm

def main():
    old, new = sys.argv[1], sys.argv[2]
    rel = "src/cmd/compile/internal/ssa/_gen/generic.rules"
    oldk = {norm(r) for _, r in g.read_rules(open(os.path.join(old, rel)).read())}
    items, skipped = [], collections.Counter()
    for ln, r in g.read_rules(open(os.path.join(new, rel)).read()):
        if norm(r) in oldk: continue
        r2 = re.sub(r"\b(ssa|ssaop)\.", "", r)
        try: insts = expand(r2)
        except ValueError: skipped["alternation"] += 1; continue
        for k, i in enumerate(insts):
            try: items.append((f"n{ln}_{k}", ln, i, g.translate(i)))
            except g.Skip as e: skipped[str(e).split(" ")[0] + " " + (str(e).split(" ")[1] if len(str(e).split(" ")) > 1 else "")] += 1
    text = g.HEADER.format(sha="new-rules", n=len(items), ex=0, sk=sum(skipped.values()))
    text = text.replace("namespace Go.Compiler.GeneratedRules", "namespace Go.Compiler.NewRules")
    text += "\n".join(g.theorem(*it) for it in items) + "\nend Go.Compiler.NewRules\n"
    out = os.path.join(g.ROOT, "build", "NewRules.lean"); open(out, "w").write(text)
    r = subprocess.run(["lake", "env", "lean", out], cwd=g.ROOT, capture_output=True, text=True, timeout=7200)
    log = r.stdout + r.stderr
    if r.returncode != 0 and ": error" not in log: raise SystemExit("lean crashed:\n" + log[-2000:])
    starts = [(text.count("\n", 0, m.start()) + 1, m.group(1)) for m in re.finditer(r"^theorem (\w+)", text, re.M)]
    res = {}
    for m in re.finditer(r"NewRules\.lean:(\d+):\d+: error: (.*)", log):
        ln = int(m.group(1)); tid = None
        for l, t in starts:
            if l <= ln: tid = t
        seg = re.split(r"\n[^\n]*\.lean:\d+:\d+: error", log[m.start():m.start() + 800], maxsplit=1)[0]
        cat = ("counterexample" if "found a counterexample" in seg and "spurious" not in seg else
               "spurious" if "spurious" in seg else "timeout" if "time" in seg else "elab_error")
        res.setdefault(tid, (cat, seg))
    c = collections.Counter(v[0] for v in res.values())
    print(f"{len(items)} new rule instances translated: {len(items) - len(res)} proved, failures {dict(c)}")
    print(f"untranslated: {dict(skipped)}")
    for tid, ln, rule, _ in items:
        if tid in res and res[tid][0] in ("counterexample", "elab_error"):
            print(f"\n{res[tid][0].upper()} {tid} generic.rules:{ln}\n  {rule[:300]}\n  {res[tid][1][:500]}")

if __name__ == "__main__":
    main()
