#!/usr/bin/env python3
"""Consistency lint for SSA rule files: flags rules that disagree with their siblings.

Three checks, each generalising a defect already found and reported:

  A. sibling shape (ARM MVNshiftRA, golang/go#82786): within one file, the shift-kind variants
     (LL/RL/RA, and their SLL/SRL/SRA helpers) of a rule must have the same right-hand side up to
     the variant. A member whose AuxInt expression drops an operator its siblings have (e.g. a
     missing ^) is reported.
  B. 64-bit count truncation (MIPS, golang/go#82776): a rule on a 64-bit shift count
     (`...x64 x (Const64 [c])`) whose condition casts the count with uint32/int32 truncates it.
  C. Size() units (PPC64, golang/go#82775): a condition comparing `.Size()` or `sizeof()` (bytes)
     with 16/32/64/128 outside vector rules probably means bits.

Output: candidates, not findings; each must be checked by hand (semantics, reachability).
Usage: rules_sibling_lint.py GEN_DIR
"""
import os, re, sys
from collections import defaultdict
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from generic_rules_to_lean import read_rules
from arm64_shift_rules import expand

SKIP = ("generic.rules", "dec.rules", "dec64.rules", "divmod.rules", "divisible.rules")


def split_rule(r):
    lhs, rhs = r.split("=>", 1)
    cond = ""
    if "&&" in lhs:
        lhs, cond = lhs.split("&&", 1)
    return lhs.strip(), cond.strip(), rhs.strip()


def aux_tag(expr):
    """Operators that matter in an AuxInt expression (shift operators removed)."""
    e = re.sub(r"<<|>>", " ", expr)
    return "".join(sorted(set(ch for ch in e if ch in "^-+*&|!")))


def norm(s, aux=True):
    s = re.sub(r"<[^<>]*>", "", s)                                  # types
    if aux:
        s = re.sub(r"\[([^\]]*)\]", lambda m: "[" + aux_tag(m.group(1)) + "]", s)
    else:
        s = re.sub(r"\[[^\]]*\]", "[]", s)
    s = re.sub(r"\{[^}]*\}", "{}", s)
    s = re.sub(r"shift(LL|RL|RA)(reg)?", r"shift*\2", s)
    s = re.sub(r"\b(SLL|SRL|SRA|SHL|SHR|SAR|SLD|SRD|SRAD|SLW|SRW|SRAW)(const)?\b", r"SHIFT\2", s)
    s = re.sub(r"\b[a-z_][a-z0-9_]*\b", "v", s)                      # pattern variables
    return re.sub(r"\s+", " ", s).strip()


def variant(lhs):
    m = re.search(r"shift(LL|RL|RA)", lhs)
    return m.group(1) if m else None


def check_siblings(path, rules, out):
    fam = defaultdict(list)
    for ln, r in rules:
        for e in expand(r):
            if "=>" not in e:
                continue
            lhs, cond, rhs = split_rule(e)
            v = variant(lhs)
            if not v:
                continue
            fam[(norm(lhs, aux=False), norm(cond, aux=False))].append((ln, v, e, norm(rhs)))
    for key, mem in fam.items():
        kinds = {v for _, v, _, _ in mem}
        if len(kinds) < 3:
            continue
        shapes = defaultdict(list)
        for m in mem:
            shapes[m[3]].append(m)
        if len(shapes) < 2:
            continue
        major = max(shapes.values(), key=len)
        for s, ms in shapes.items():
            if ms is major or len(ms) >= len(major):
                continue
            for ln, v, e, _ in ms:
                out.append(("A sibling-shape", os.path.basename(path), ln, e,
                            f"siblings ({len(major)}) look like: {major[0][2]}"))


def wkey(s):
    """Normalise operand widths in op names: Rsh8x64 -> RshNxN, MOVBreg -> MOVwreg, ...CMPW -> CMPw."""
    s = re.sub(r"\b([A-Z][A-Za-z]*?)(8|16|32|64)(U?)x(8|16|32|64)\b", r"\1N\3xN", s)
    s = re.sub(r"\b([A-Z][A-Za-z]*?)(8|16|32|64)(U?)(F?)\b", r"\1N\3\4", s)
    s = re.sub(r"\bMOV(B|H|W|D|V|Q|L)(Z|U)?(reg|load|store|const)\b", r"MOVw\2\3", s)
    return s


def check_width_siblings(path, rules, out):
    fam = defaultdict(list)
    for ln, r in rules:
        for e in expand(r):
            if "=>" not in e:
                continue
            lhs, cond, rhs = split_rule(e)
            k = wkey(norm(lhs, aux=False))
            if k == norm(lhs, aux=False):
                continue
            # keep only rules whose RHS folds to a constant: there the AuxInt expression carries
            # the semantics, and operator sets should not depend on the width
            m = re.match(r"\((?:MOV[A-Z]*const|Const\d+F?|MOVDconst|MOVWconst|MOVVconst|MOVQconst|MOVLconst|I64Const)\b[^\[]*\[([^\]]*)\]\)$", rhs)
            if not m:
                continue
            fam[(k, wkey(norm(cond, aux=False)))].append((ln, e, aux_tag(m.group(1))))
    for key, mem in fam.items():
        if len(mem) < 3:
            continue
        tags = defaultdict(list)
        for x in mem:
            tags[x[2]].append(x)
        if len(tags) < 2:
            continue
        major = max(tags.values(), key=len)
        for t, ms in tags.items():
            if ms is major or len(ms) * 2 > len(major):
                continue
            for ln, e, _ in ms:
                out.append(("A2 width-shape", os.path.basename(path), ln, e,
                            f"width siblings ({len(major)}) fold with operators '{major[0][2]}', e.g. {major[0][1]}"))


def check_count_casts(path, rules, out):
    for ln, r in rules:
        for e in expand(r):
            if "=>" not in e:
                continue
            lhs, cond, rhs = split_rule(e)
            m = re.match(r"\((Lsh|Rsh)\d+U?x64\b", lhs)
            if not m or "(Const64 [c])" not in lhs:
                continue
            if re.search(r"\b(u?int32)\(c\)", cond):
                out.append(("B count-cast", os.path.basename(path), ln, e,
                            "64-bit constant count tested through a 32-bit cast"))


def check_size_units(path, rules, out):
    for ln, r in rules:
        for e in expand(r):
            if "=>" not in e:
                continue
            lhs, cond, rhs = split_rule(e)
            if re.search(r"\bV[A-Z]|Vec|SIMD|IsSIMD|Zero128|Mask|FMOVQ|V128|ZLDR|ZSTR", lhs + rhs + cond):
                continue
            for m in re.finditer(r"(\.Size\(\)|sizeof\([^)]*\))\s*(<=|<|==|>=|>|!=)\s*(16|32|64|128)\b", cond):
                out.append(("C size-units", os.path.basename(path), ln, e,
                            f"`{m.group(0)}`: Size() is in bytes"))


def main():
    gen = sys.argv[1]
    out = []
    for f in sorted(os.listdir(gen)):
        if not f.endswith(".rules") or f in SKIP:
            continue
        p = os.path.join(gen, f)
        rules = read_rules(open(p).read())
        check_siblings(p, rules, out)
        check_width_siblings(p, rules, out)
        check_count_casts(p, rules, out)
        check_size_units(p, rules, out)
    seen = set()
    for kind, f, ln, e, why in out:
        k = (kind, f, ln, e)
        if k in seen:
            continue
        seen.add(k)
        print(f"{kind}  {f}:{ln}\n    {e}\n    -> {why}")
    counts = defaultdict(int)
    for kind, *_ in out:
        counts[kind] += 1
    print("summary:", dict(counts))


if __name__ == "__main__":
    main()
