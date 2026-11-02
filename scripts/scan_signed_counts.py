#!/usr/bin/env python3
"""Lint: rules whose condition or AuxInt arithmetic treats a constant SHIFT COUNT as signed.

A Go shift count is unsigned. In SSA a constant count is an int64 AuxInt, so values >= 2^63
are negative. The class of golang/go#82763: a signed comparison (`c < e`, `c >= d`) or signed
arithmetic (`c-e`, `c+d`) on such a count, with no guard (`c >= 0`, `uint64(c) < N`,
`!uaddOvf`, `0 <= c`, `c < N` with a small literal N also being signed!) restricting it to
[0, 2^63). Output: candidate rules for Lean checking; NOT findings.

Usage: scan_signed_counts.py <dir with *.rules>
"""
import glob, os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generic_rules_to_lean import read_rules
from arm64_shift_rules import expand

# generic: second argument of a Go shift op is the count
GEN_SHIFT = re.compile(r"\((?:Lsh|Rsh)\d+U?x64\b[^()]*?(?:\([^()]*\)|\w+|_)\s+\(Const64\s+(?:<[^>]*>\s+)?\[(\w+)\]\)\)")

def count_vars(lhs):
    return set(GEN_SHIFT.findall(lhs))

def guarded(v, cond):
    c = cond.replace(" ", "")
    pats = [rf"\b{v}>=0", rf"0<={v}\b", rf"uint64\({v}\)<", rf"uint64\({v}\)<=", rf"{v}>0\b", rf"0<{v}\b",
            rf"uint64\({v}\)>=", rf"uint64\({v}\)>"]
    return any(re.search(p, c) for p in pats)

def signed_uses(v, cond, rhs):
    uses = []
    c = cond.replace(" ", "")
    for m in re.finditer(rf"(?<![\w(])({v})(<=|>=|<|>|==)(\w+)|(\w+)(<=|>=|<|>)({v})\b", c):
        s = m.group(0)
        if f"uint64({v})" in c and re.search(rf"uint64\({v}\)", s): continue
        uses.append(("cond", s))
    for m in re.finditer(rf"\[([^\]]*\b{v}\b[^\]]*)\]", rhs):
        e = m.group(1).replace(" ", "")
        if re.search(rf"\b{v}\b[-+]|[-+]\b{v}\b", e) and f"uint64({v}" not in e:
            uses.append(("rhs", e))
    return uses

def main():
    d = sys.argv[1]
    total = 0
    for f in sorted(glob.glob(os.path.join(d, "*.rules"))):
        src = open(f).read()
        for ln, rule in read_rules(src):
            try: insts = expand(rule)
            except ValueError: insts = [rule]
            r = insts[0]
            lhs, rhs = r.split("=>", 1)
            cond = lhs.split("&&", 1)[1] if "&&" in lhs else ""
            for v in count_vars(lhs.split("&&", 1)[0]):
                uses = signed_uses(v, cond, rhs)
                if uses and not guarded(v, cond):
                    total += 1
                    print(f"{os.path.basename(f)}:{ln}: count `{v}` used signed {uses}\n    {rule[:230]}")
    print(f"{total} candidate rules")

if __name__ == "__main__":
    main()
