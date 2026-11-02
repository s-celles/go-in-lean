#!/usr/bin/env python3
"""Semantic diff of SSA rule files between two GOROOTs (e.g. a release and master).

Rules are read with the multi-line reader of generic_rules_to_lean.py, alternations are kept,
and the text is normalised (whitespace, `ssa.`/`ssaop.`/`typ.` package qualifiers that master
added during a refactor, trailing comments). Prints rules present only in NEW, grouped by file.
Usage: rules_diff.py OLD_GEN_DIR NEW_GEN_DIR [file.rules ...]
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generic_rules_to_lean import read_rules

def norm(r):
    r = re.sub(r"\b(ssa|ssaop|ssabase)\.", "", r)
    r = re.sub(r"\s+", " ", r).strip()
    r = re.sub(r"\(\s+", "(", r); r = re.sub(r"\s+\)", ")", r)
    return r

def rules(path):
    if not os.path.exists(path): return {}
    return {norm(r): (ln, r) for ln, r in read_rules(open(path).read())}

def main():
    old, new = sys.argv[1], sys.argv[2]
    files = sys.argv[3:] or sorted(f for f in os.listdir(new) if f.endswith(".rules"))
    total = 0
    for f in files:
        a, b = rules(os.path.join(old, f)), rules(os.path.join(new, f))
        added = [b[k] for k in b if k not in a]
        removed = [a[k] for k in a if k not in b]
        if not added and not removed: continue
        print(f"== {f}: +{len(added)} -{len(removed)}")
        for ln, r in sorted(added):
            print(f"  + {f}:{ln}: {r[:220]}")
        total += len(added)
    print(f"{total} added rules")

if __name__ == "__main__":
    main()
