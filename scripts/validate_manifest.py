#!/usr/bin/env python3
"""Validate targets/properties.yaml against the audited Lean environment and the Go tests.

Checks:
* schema: every property has the required fields and a legal status;
* every `lean_theorem` exists in the audit output (lake exe audit --json), is
  not SORRY/FORBIDDEN, and the recorded `trust` tier matches the audit;
* statuses `proved_in_model` require a theorem; `counterexample_in_model`,
  `model_mismatch`, `go_discrepancy_reproduced`, `known_issue` require a
  `finding` or `evidence` entry; `inconclusive` requires a `blocker`;
* every referenced Go test function exists in go/tests or go/reproducers;
* ids are unique and history entries are chronological.

Uses only the standard library (a tiny YAML subset parser) so that CI needs
no extra Python packages.
"""
import json, os, re, sys

STATUSES = {"proved_in_model", "counterexample_in_model", "model_mismatch",
            "specification_ambiguity", "go_discrepancy_reproduced", "known_issue", "inconclusive"}
REQUIRED = ["id", "package", "function", "go_source", "doc", "preconditions", "postcondition",
            "lean_statement", "oracle", "ambiguity_risk", "complexity", "status", "history"]

def parse_yaml(text):
    """Minimal YAML subset: top-level `properties:` list of mappings, scalars, inline lists,
    nested lists of mappings (history), block scalars with `>`/`|` not supported."""
    lines = [l.rstrip("\n") for l in text.splitlines()]
    items, cur, hist, in_hist = [], None, None, False
    for raw in lines:
        if not raw.strip() or raw.lstrip().startswith("#"):
            continue
        indent = len(raw) - len(raw.lstrip())
        line = raw.strip()
        if indent == 0:
            if line != "properties:":
                raise SystemExit(f"unexpected top-level line: {raw}")
            continue
        if indent == 2 and line.startswith("- "):
            cur = {}; items.append(cur); in_hist = False
            line = line[2:]; indent = 4
        if indent == 4 and not in_hist or (indent == 4 and in_hist and not line.startswith("- ")):
            in_hist = False
            k, _, v = line.partition(":")
            v = v.strip()
            if k == "history" and v == "":
                cur["history"] = []; in_hist = True; continue
            cur[k.strip()] = scalar(v)
            continue
        if in_hist:
            if indent == 6 and line.startswith("- "):
                body = line[2:].strip()
                if body.startswith("{"):
                    cur["history"].append(scalar(body)); continue
                hist = {}; cur["history"].append(hist); line = body
            k, _, v = line.partition(":")
            hist[k.strip()] = scalar(v.strip())
            continue
        raise SystemExit(f"cannot parse line: {raw}")
    return items

def split_top(inner, sep=","):
    """Split on `sep` outside quotes/brackets."""
    parts, depth, q, cur = [], 0, None, ""
    for ch in inner:
        if q:
            cur += ch
            if ch == q:
                q = None
            continue
        if ch in "\"'":
            q = ch; cur += ch; continue
        if ch in "[{":
            depth += 1
        elif ch in "]}":
            depth -= 1
        if ch == sep and depth == 0:
            parts.append(cur); cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return parts

def scalar(v):
    if v.startswith("{") and v.endswith("}"):
        inner = v[1:-1].strip()
        out = {}
        for part in split_top(inner):
            k, _, val = part.partition(":")
            out[k.strip()] = scalar(val.strip())
        return out
    if v.startswith("[") and v.endswith("]"):
        inner = v[1:-1].strip()
        return [scalar(x.strip()) for x in split_top(inner)] if inner else []
    if (v.startswith('"') and v.endswith('"')) or (v.startswith("'") and v.endswith("'")):
        return v[1:-1]
    if v in ("true", "false"):
        return v == "true"
    if v == "null" or v == "~":
        return None
    return v

def go_test_names(root):
    names = set()
    for d in ("go/tests", "go/reproducers"):
        p = os.path.join(root, d)
        if not os.path.isdir(p):
            continue
        for f in os.listdir(p):
            if f.endswith("_test.go"):
                src = open(os.path.join(p, f)).read()
                names |= set(re.findall(r"^func (Test\w+|Fuzz\w+)\(", src, re.M))
    return names

def main():
    manifest, audit_path = sys.argv[1], sys.argv[2]
    root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    props = parse_yaml(open(manifest).read())
    audit = {r["name"]: r for r in json.load(open(audit_path))}
    gotests = go_test_names(root)
    errors, ids = [], set()
    for p in props:
        pid = p.get("id", "<no id>")
        for k in REQUIRED:
            if k not in p:
                errors.append(f"{pid}: missing field {k}")
        if pid in ids:
            errors.append(f"{pid}: duplicate id")
        ids.add(pid)
        st = p.get("status")
        if st not in STATUSES:
            errors.append(f"{pid}: illegal status {st}")
        thms = p.get("lean_theorem") or []
        if isinstance(thms, str):
            thms = [thms]
        tiers = set()
        for t in thms:
            row = audit.get(t)
            if row is None:
                errors.append(f"{pid}: theorem {t} not found in audit")
                continue
            if row["tier"] in ("SORRY", "FORBIDDEN"):
                errors.append(f"{pid}: theorem {t} has tier {row['tier']}")
            tiers.add(row["tier"])
        # the entry's trust tier is the weakest tier among its theorems
        if thms and p.get("trust"):
            entry_tier = "bv_decide" if "bv_decide" in tiers else "kernel"
            if p["trust"] != entry_tier:
                errors.append(f"{pid}: trust {p['trust']} but audit says {entry_tier} (theorem tiers {sorted(tiers)})")
        if st == "proved_in_model" and not thms:
            errors.append(f"{pid}: proved_in_model without lean_theorem")
        if st in ("counterexample_in_model", "model_mismatch", "go_discrepancy_reproduced", "known_issue") \
                and not (p.get("finding") or p.get("evidence")):
            errors.append(f"{pid}: status {st} needs finding or evidence")
        if st == "inconclusive" and not p.get("blocker"):
            errors.append(f"{pid}: inconclusive without blocker")
        for gt in p.get("go_tests") or []:
            if gt not in gotests:
                errors.append(f"{pid}: Go test {gt} not found")
        hist = p.get("history") or []
        if not hist:
            errors.append(f"{pid}: empty history")
        dates = [h.get("date", "") for h in hist]
        if dates != sorted(dates):
            errors.append(f"{pid}: history not chronological")
        if hist and hist[-1].get("status") != st:
            errors.append(f"{pid}: last history status {hist[-1].get('status')} != status {st}")
    by_status = {}
    for p in props:
        by_status[p.get("status")] = by_status.get(p.get("status"), 0) + 1
    print(f"{len(props)} properties: " + ", ".join(f"{k}={v}" for k, v in sorted(by_status.items())))
    if errors:
        print("MANIFEST ERRORS:")
        for e in errors:
            print("  " + e)
        sys.exit(1)
    print("manifest ok")

if __name__ == "__main__":
    main()
