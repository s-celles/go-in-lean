#!/usr/bin/env python3
"""Differentially probe narrow-value spill restores across a call.

The amd64 build is the semantic control.  Each target build keeps a value such
as int16(uint16(int8(-1))) live across a noinline call, then uses it in a signed
comparison and a widening conversion.  Varying the number of other live call
arguments finds the pressure threshold where regalloc spills the value.
"""

from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess


WIDTHS = ((8, 8), (8, 16), (16, 32), (32, 64))


def program(source_bits: int, value_bits: int, pressure: int) -> str:
    source_type = f"int{source_bits}"
    value_type = f"int{value_bits}"
    unsigned_type = f"uint{value_bits}"
    params = [f"a{i} int64" for i in range(pressure + 1)]
    xor = " ^ ".join(f"a{i}" for i in range(pressure + 1))
    locals_ = "\n".join(
        f"\ta{i} := x + {i}" for i in range(1, pressure + 1)
    )
    args = ["int64(v)"] + [f"a{i}" for i in range(1, pressure + 1)]
    return f'''package main

import "fmt"

//go:noinline
func clobber({", ".join(params)}) int64 {{ return {xor} }}

//go:noinline
func probe(y {source_type}, k {value_type}, x int64) int64 {{
\tv := {value_type}({unsigned_type}(y))
{locals_}
\tz := clobber({", ".join(args)})
\tif v >= k {{ return z + int64(v) + 1000 }}
\treturn z + int64(v) - 1000
}}

func main() {{ fmt.Println(probe(-1, 9, 100)) }}
'''


def command(
    argv: list[str], cwd: Path, env: dict[str, str]
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--go", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--goarch", required=True)
    parser.add_argument("--runner", required=True)
    parser.add_argument("--max-pressure", type=int, default=20)
    parser.add_argument("--target-env", action="append", default=[])
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    runner = shlex.split(args.runner)

    base_env = os.environ.copy()
    base_env.update(GOOS="linux", GOTOOLCHAIN="local", CGO_ENABLED="0")
    target_env = base_env.copy()
    target_env["GOARCH"] = args.goarch
    for assignment in args.target_env:
        key, value = assignment.split("=", 1)
        target_env[key] = value
    native_env = base_env.copy()
    native_env["GOARCH"] = "amd64"

    results: list[dict[str, object]] = []
    for source_bits, value_bits in WIDTHS:
        for pressure in range(args.max_pressure + 1):
            name = f"i{source_bits}_u{value_bits}_i{value_bits}_p{pressure}"
            case_dir = args.out / name
            case_dir.mkdir()
            source = case_dir / "main.go"
            source.write_text(program(source_bits, value_bits, pressure))
            formatted = command([args.go, "fmt", "main.go"], case_dir, native_env)
            if formatted.returncode:
                results.append({"name": name, "status": "format_error", "diagnostic": formatted.stderr})
                continue

            native_build = command([args.go, "build", "-o", "native", "main.go"], case_dir, native_env)
            target_build = command([args.go, "build", "-o", "target", "main.go"], case_dir, target_env)
            if native_build.returncode or target_build.returncode:
                results.append(
                    {
                        "name": name,
                        "status": "build_error",
                        "diagnostic": native_build.stdout + native_build.stderr + target_build.stdout + target_build.stderr,
                    }
                )
                continue
            native = command([str(case_dir / "native")], case_dir, native_env)
            target = command(runner + [str(case_dir / "target")], case_dir, target_env)
            if native.returncode or target.returncode:
                results.append(
                    {
                        "name": name,
                        "status": "run_error",
                        "diagnostic": native.stderr + target.stderr,
                    }
                )
                continue
            status = "mismatch" if native.stdout != target.stdout else "ok"
            results.append(
                {
                    "name": name,
                    "source_bits": source_bits,
                    "value_bits": value_bits,
                    "pressure": pressure,
                    "status": status,
                    "native": native.stdout.strip(),
                    "target": target.stdout.strip(),
                }
            )
            if status == "ok":
                shutil.rmtree(case_dir)

    failures = [result for result in results if result["status"] != "ok"]
    report = {
        "go_version": command([args.go, "version"], args.out, base_env).stdout.strip(),
        "goarch": args.goarch,
        "failures": failures,
        "total": len(results),
    }
    report_path = args.out / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(f"{args.goarch}: {len(failures)} mismatches/errors / {len(results)} cases")
    for failure in failures:
        print(
            f"{failure['name']}: {failure['status']} "
            f"{failure.get('native', '')} -> {failure.get('target', '')}"
        )
    print(report_path)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
