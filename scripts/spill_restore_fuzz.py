#!/usr/bin/env python3
"""Differentially probe narrow-value spill restores across a call.

The amd64 build is the semantic control. Each target build keeps a value whose
SSA type can disagree with the extension already present in its register live
across a noinline call, then observes it through both a signed comparison and a
widening conversion. The audit suite varies:

* every widening pair among 8, 16, 32, and 64 bits;
* sign-over-zero and zero-over-sign extension chains;
* argument, load, call, arithmetic, shift, rotate, reverse-byte, and Phi
  producers; and
* register pressure, to move the value across the spill/restore boundary.

Successful case directories are removed. A mismatch retains its Go source and
binaries next to report.json so that it can be minimized and disassembled.
"""

from __future__ import annotations

import argparse
import concurrent.futures
from dataclasses import dataclass
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess


ALL_WIDTHS = (8, 16, 32, 64)
LEGACY_WIDTHS = ((8, 8), (8, 16), (16, 32), (32, 64))
AUDIT_FAMILIES = (
    "arg",
    "load",
    "call",
    "shift",
    "mul",
    "phi",
    "rotate",
    "reverse",
)


@dataclass(frozen=True)
class Case:
    extension: str
    family: str
    source_bits: int
    value_bits: int
    pressure: int

    @property
    def name(self) -> str:
        prefix = "" if self.extension == "sign" else f"{self.extension}_"
        return (
            f"{prefix}{self.family}_i{self.source_bits}_u{self.value_bits}_"
            f"i{self.value_bits}_p{self.pressure}"
        )


def producer(case: Case) -> tuple[str, str, str, bool]:
    """Return prefix, narrow expression, main input, and bits-import use."""
    source_type = f"int{case.source_bits}"
    unsigned_source = f"uint{case.source_bits}"
    family = case.family
    if family == "arg":
        return "", "y", "-1", False
    if family == "load":
        return "", f"load{case.source_bits}(&y)", "-1", False
    if family == "call":
        return "", f"source{case.source_bits}(y)", "-1", False
    if family == "shift":
        return "", f"{source_type}(y >> 1)", "-1", False
    if family == "mul":
        return "", f"{source_type}(y * 3)", "-1", False
    if family == "phi":
        return (
            f"\tvar narrow {source_type}\n"
            "\tif flag {\n"
            "\t\tnarrow = y\n"
            "\t} else {\n"
            f"\t\tnarrow = {source_type}(y + 1)\n"
            "\t}",
            "narrow",
            "-1",
            False,
        )
    if family == "rotate":
        return (
            "",
            f"{source_type}(bits.RotateLeft{case.source_bits}("
            f"{unsigned_source}(y), 1))",
            "-1",
            True,
        )
    if family == "reverse":
        return (
            "",
            f"{source_type}(bits.ReverseBytes{case.source_bits}("
            f"{unsigned_source}(y)))",
            "-2",
            True,
        )
    raise ValueError(f"unknown producer family: {family}")


def program(case: Case) -> str:
    source_type = f"int{case.source_bits}"
    signed_type = f"int{case.value_bits}"
    unsigned_type = f"uint{case.value_bits}"
    if case.extension == "sign":
        value_type = signed_type
        wide_type = "int64"
        value_expr = f"{signed_type}({unsigned_type}({{narrow}}))"
    else:
        value_type = unsigned_type
        wide_type = "uint64"
        value_expr = f"{unsigned_type}({signed_type}({{narrow}}))"
    params = [f"a{i} {wide_type}" for i in range(case.pressure + 1)]
    xor = " ^ ".join(f"a{i}" for i in range(case.pressure + 1))
    locals_ = "\n".join(
        f"\ta{i} := x + {i}" for i in range(1, case.pressure + 1)
    )
    args = [f"{wide_type}(v)"] + [f"a{i}" for i in range(1, case.pressure + 1)]
    prefix, narrow, input_value, uses_bits = producer(case)
    flag_param = ", flag bool" if case.family == "phi" else ""
    flag_arg = ", true" if case.family == "phi" else ""
    imports = 'import "fmt"'
    if uses_bits:
        imports = 'import (\n\t"fmt"\n\t"math/bits"\n)'
    helpers = ""
    if case.family == "load":
        helpers = f'''//go:noinline
func load{case.source_bits}(p *{source_type}) {source_type} {{ return *p }}

'''
    elif case.family == "call":
        helpers = f'''//go:noinline
func source{case.source_bits}(x {source_type}) {source_type} {{ return x }}

'''
    return f'''package main

{imports}

{helpers}//go:noinline
func clobber({", ".join(params)}) {wide_type} {{ return {xor} }}

//go:noinline
func probe(y {source_type}, k {value_type}{flag_param}, x {wide_type}) {wide_type} {{
{prefix}
\tv := {value_expr.format(narrow=narrow)}
{locals_}
\tz := clobber({", ".join(args)})
\tif v >= k {{ return z + {wide_type}(v) + 1000 }}
\treturn z + {wide_type}(v) - 1000
}}

func main() {{ fmt.Println(probe({input_value}, 9{flag_arg}, 100)) }}
'''


def command(
    argv: list[str], cwd: Path, env: dict[str, str]
) -> subprocess.CompletedProcess[str]:
    return subprocess.run(argv, cwd=cwd, env=env, text=True, capture_output=True)


def run_case(
    case: Case,
    *,
    args: argparse.Namespace,
    native_env: dict[str, str],
    target_env: dict[str, str],
    runner: list[str],
) -> dict[str, object]:
    case_dir = args.out / case.name
    if case_dir.exists():
        shutil.rmtree(case_dir)
    case_dir.mkdir()
    source = case_dir / "main.go"
    source.write_text(program(case))
    record: dict[str, object] = {
        "name": case.name,
        "extension": case.extension,
        "family": case.family,
        "source_bits": case.source_bits,
        "value_bits": case.value_bits,
        "pressure": case.pressure,
    }

    formatted = command([args.go, "fmt", "main.go"], case_dir, native_env)
    if formatted.returncode:
        record.update(status="format_error", diagnostic=formatted.stdout + formatted.stderr)
        return record

    native_build = command(
        [args.go, "build", "-o", "native", "main.go"], case_dir, native_env
    )
    target_build = command(
        [args.go, "build", "-o", "target", "main.go"], case_dir, target_env
    )
    if native_build.returncode or target_build.returncode:
        record.update(
            status="build_error",
            diagnostic=(
                native_build.stdout
                + native_build.stderr
                + target_build.stdout
                + target_build.stderr
            ),
        )
        return record
    native = command([str(case_dir / "native")], case_dir, native_env)
    target = command(runner + [str(case_dir / "target")], case_dir, target_env)
    if native.returncode or target.returncode:
        record.update(
            status="run_error",
            diagnostic=native.stdout + native.stderr + target.stdout + target.stderr,
        )
        return record
    status = "mismatch" if native.stdout != target.stdout else "ok"
    record.update(
        status=status,
        native=native.stdout.strip(),
        target=target.stdout.strip(),
    )
    if status == "ok":
        shutil.rmtree(case_dir)
    return record


def audit_cases(
    max_pressure: int,
    families: tuple[str, ...],
    extensions: tuple[str, ...] = ("sign", "zero"),
) -> list[Case]:
    widths = [
        (source, value)
        for source in ALL_WIDTHS
        for value in ALL_WIDTHS
        if source < value
    ]
    return [
        Case(extension, family, source, value, pressure)
        for extension in extensions
        for family in families
        for source, value in widths
        if family != "reverse" or source >= 16
        for pressure in range(max_pressure + 1)
    ]


def legacy_cases(max_pressure: int) -> list[Case]:
    return [
        Case("sign", "arg", source, value, pressure)
        for source, value in LEGACY_WIDTHS
        for pressure in range(max_pressure + 1)
    ]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--go", required=True)
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--goarch", required=True)
    parser.add_argument("--runner", default="")
    parser.add_argument("--max-pressure", type=int, default=20)
    parser.add_argument("--jobs", type=int, default=min(8, os.cpu_count() or 1))
    parser.add_argument("--suite", choices=("audit", "legacy"), default="audit")
    parser.add_argument(
        "--families",
        default=",".join(AUDIT_FAMILIES),
        help="comma-separated producer families for the audit suite",
    )
    parser.add_argument(
        "--extensions",
        default="sign,zero",
        help="comma-separated extension directions: sign,zero",
    )
    parser.add_argument("--target-env", action="append", default=[])
    args = parser.parse_args()
    args.out.mkdir(parents=True, exist_ok=True)
    # Commands run with each case directory as cwd, so retain an absolute path
    # for executing the just-built binaries even when --out was relative.
    args.out = args.out.resolve()
    runner = shlex.split(args.runner)

    base_env = os.environ.copy()
    base_env.update(
        GOOS="linux",
        GOTOOLCHAIN="local",
        GO111MODULE="off",
        CGO_ENABLED="0",
    )
    target_env = base_env.copy()
    target_env["GOARCH"] = args.goarch
    for assignment in args.target_env:
        key, value = assignment.split("=", 1)
        target_env[key] = value
    native_env = base_env.copy()
    native_env["GOARCH"] = "amd64"

    if args.suite == "legacy":
        cases = legacy_cases(args.max_pressure)
    else:
        families = tuple(filter(None, args.families.split(",")))
        unknown = sorted(set(families) - set(AUDIT_FAMILIES))
        if unknown:
            parser.error(f"unknown families: {', '.join(unknown)}")
        extensions = tuple(filter(None, args.extensions.split(",")))
        unknown_extensions = sorted(set(extensions) - {"sign", "zero"})
        if unknown_extensions:
            parser.error(f"unknown extensions: {', '.join(unknown_extensions)}")
        cases = audit_cases(args.max_pressure, families, extensions)

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(
            pool.map(
                lambda case: run_case(
                    case,
                    args=args,
                    native_env=native_env,
                    target_env=target_env,
                    runner=runner,
                ),
                cases,
            )
        )

    failures = [result for result in results if result["status"] != "ok"]
    report = {
        "go_version": command(
            [args.go, "version"], args.out, base_env
        ).stdout.strip(),
        "goarch": args.goarch,
        "suite": args.suite,
        "families": sorted({case.family for case in cases}),
        "extensions": sorted({case.extension for case in cases}),
        "max_pressure": args.max_pressure,
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
