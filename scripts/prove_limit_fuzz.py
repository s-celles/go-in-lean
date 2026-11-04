#!/usr/bin/env python3
"""Probe cmd/compile's prove pass at narrow-integer limit boundaries.

The generator concentrates on nested constant shifts.  Generic SSA rewrites
combine their counts, and a count carrying the shifted value's narrow type can
make ssa.InitLimit produce contradictory signed bounds.  Compile every case in
isolation so one compiler panic does not hide the rest of the matrix.

Usage:
    prove_limit_fuzz.py --go /path/to/go --out /tmp/prove-limit
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import re
import subprocess
import tempfile


PANIC_RE = re.compile(r"(?:internal compiler error|panic:|negative shift amount)")


def totals(bits: int) -> list[int]:
    sign = 1 << (bits - 1)
    modulus = 1 << bits
    candidates = {
        bits - 1,
        bits,
        sign - 1,
        sign,
        sign + 1,
        modulus - 1,
        modulus,
        modulus + 1,
        modulus + sign - 1,
        modulus + sign,
        modulus + sign + 1,
    }
    return sorted(candidates)


def splits(total: int) -> list[tuple[int, int]]:
    pairs = {(1, total - 1), (total // 2, total - total // 2)}
    return sorted(pair for pair in pairs if pair[0] >= 0 and pair[1] >= 0)


def triple_splits(total: int) -> list[tuple[int, int, int]]:
    third = total // 3
    triples = {(1, 1, total - 2), (third, third, total - 2 * third)}
    return sorted(parts for parts in triples if min(parts) >= 0)


def cases() -> list[dict[str, object]]:
    result: list[dict[str, object]] = []
    for bits in (8, 16, 32):
        for signed in (True, False):
            typ = ("int" if signed else "uint") + str(bits)
            for operator, opname in ((">>", "rsh"), ("<<", "lsh")):
                for total in totals(bits):
                    for left, right in splits(total):
                        name = f"{opname}_{typ}_{left}_{right}"
                        result.append(
                            {
                                "name": name,
                                "type": typ,
                                "operator": operator,
                                "counts": [left, right],
                                "total": total,
                            }
                        )
        typ = "int" + str(bits)
        for total in totals(bits):
            for parts in triple_splits(total):
                joined = "_".join(str(part) for part in parts)
                result.append(
                    {
                        "name": f"rsh3_{typ}_{joined}",
                        "type": typ,
                        "operator": ">>",
                        "counts": list(parts),
                        "total": total,
                    }
                )
    return result


def source(case: dict[str, object]) -> str:
    typ = case["type"]
    op = case["operator"]
    expression = "y"
    for count in case["counts"]:
        expression = f"({expression} {op} uint64({count}))"
    return (
        "package p\n\n"
        f"func F(y {typ}) {typ} {{\n"
        f"\treturn {expression}\n"
        "}\n"
    )


def compile_case(go: str, root: Path, case: dict[str, object]) -> dict[str, object]:
    name = str(case["name"])
    case_dir = root / name
    case_dir.mkdir()
    go_file = case_dir / "repro.go"
    go_file.write_text(source(case))
    proc = subprocess.run(
        [go, "tool", "compile", "-o", os.devnull, str(go_file)],
        text=True,
        capture_output=True,
    )
    diagnostic = proc.stdout + proc.stderr
    if proc.returncode == 0:
        status = "ok"
    elif PANIC_RE.search(diagnostic):
        status = "ice"
    else:
        status = "compile_error"
    record = dict(case)
    record.update(
        {
            "status": status,
            "returncode": proc.returncode,
            "diagnostic": diagnostic,
        }
    )
    if status == "ok":
        go_file.unlink()
        case_dir.rmdir()
    else:
        (case_dir / "diagnostic.txt").write_text(diagnostic)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--go", default=os.environ.get("GO", "go"))
    parser.add_argument("--out", type=Path)
    parser.add_argument("--jobs", type=int, default=min(12, os.cpu_count() or 1))
    args = parser.parse_args()

    version = subprocess.run(
        [args.go, "version"], text=True, capture_output=True, check=True
    ).stdout.strip()
    if args.out is None:
        out = Path(tempfile.mkdtemp(prefix="prove-limit-"))
    else:
        out = args.out
        out.mkdir(parents=True, exist_ok=True)

    matrix = cases()
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(lambda c: compile_case(args.go, out, c), matrix))

    summary = {
        "go_version": version,
        "total": len(results),
        "ok": sum(r["status"] == "ok" for r in results),
        "ice": sum(r["status"] == "ice" for r in results),
        "compile_error": sum(r["status"] == "compile_error" for r in results),
        "results": results,
    }
    report = out / "report.json"
    report.write_text(json.dumps(summary, indent=2) + "\n")
    print(f"{version}: {summary['ice']} ICE, {summary['ok']} clean, "
          f"{summary['compile_error']} other errors / {summary['total']} cases")
    print(report)
    for item in results:
        if item["status"] == "ice":
            first = next(
                (line for line in str(item["diagnostic"]).splitlines() if line.strip()),
                "",
            )
            print(f"ICE {item['name']}: {first}")
    return 1 if summary["ice"] or summary["compile_error"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
