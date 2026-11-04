#!/usr/bin/env python3
"""Differential campaign for cmd/compile's decomposeAddr SSA pass.

For each seed, generate one aggregate-heavy Go program, build it normally and
with decomposeAddr disabled, execute both binaries, and compare their output.
Successful seed directories are removed; failures retain sources, binaries,
and diagnostics below --out.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import json
import os
from pathlib import Path
import shlex
import shutil
import subprocess
import sys


def run(
    command: list[str],
    *,
    cwd: Path,
    env: dict[str, str],
    timeout: int,
) -> subprocess.CompletedProcess[str]:
    try:
        return subprocess.run(
            command,
            cwd=cwd,
            env=env,
            text=True,
            capture_output=True,
            timeout=timeout,
        )
    except subprocess.TimeoutExpired as exc:
        stdout = exc.stdout or ""
        stderr = exc.stderr or ""
        return subprocess.CompletedProcess(command, 124, stdout, stderr + "\ntimeout\n")


def one_seed(
    seed: int,
    *,
    args: argparse.Namespace,
    base_env: dict[str, str],
    runner: list[str],
) -> dict[str, object]:
    seed_dir = args.out / f"seed-{seed}"
    seed_dir.mkdir(parents=True)
    generated = run(
        [sys.executable, str(args.generator), str(seed), str(args.functions), str(seed_dir)],
        cwd=args.generator.parent,
        env=base_env,
        timeout=args.timeout,
    )
    record: dict[str, object] = {"seed": seed}
    if generated.returncode:
        record.update(status="generate_error", diagnostic=generated.stdout + generated.stderr)
        return record

    builds: dict[str, subprocess.CompletedProcess[str]] = {}
    builds["on"] = run(
        [args.go, "build", "-o", "on", "."],
        cwd=seed_dir,
        env=base_env,
        timeout=args.timeout,
    )
    builds["off"] = run(
        [args.go, "build", "-gcflags=-d=ssa/decompose_addr/off", "-o", "off", "."],
        cwd=seed_dir,
        env=base_env,
        timeout=args.timeout,
    )
    for mode in ("on", "off"):
        proc = builds[mode]
        if proc.returncode:
            record.update(
                status=f"build_{mode}_error",
                diagnostic=proc.stdout + proc.stderr,
            )
            return record

    outputs: dict[str, str] = {}
    for mode in ("on", "off"):
        proc = run(
            runner + [str(seed_dir / mode)],
            cwd=seed_dir,
            env=base_env,
            timeout=args.timeout,
        )
        if proc.returncode:
            record.update(
                status=f"run_{mode}_error",
                diagnostic=proc.stdout + proc.stderr,
            )
            return record
        outputs[mode] = proc.stdout

    if outputs["on"] != outputs["off"]:
        record.update(status="mismatch", on=outputs["on"], off=outputs["off"])
        return record

    record.update(status="ok", output=outputs["on"].strip())
    shutil.rmtree(seed_dir)
    return record


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--go", required=True)
    parser.add_argument(
        "--generator",
        type=Path,
        default=Path(__file__).with_name("decompose_addr_fuzz.py"),
    )
    parser.add_argument("--out", type=Path, required=True)
    parser.add_argument("--first", type=int, default=1)
    parser.add_argument("--count", type=int, default=100)
    parser.add_argument("--functions", type=int, default=60)
    parser.add_argument("--jobs", type=int, default=min(12, os.cpu_count() or 1))
    parser.add_argument("--timeout", type=int, default=120)
    parser.add_argument("--goos", default="linux")
    parser.add_argument("--goarch", default="amd64")
    parser.add_argument("--goamd64")
    parser.add_argument(
        "--runner",
        default="",
        help="command prepended to a cross-compiled binary, e.g. 'qemu-aarch64'",
    )
    args = parser.parse_args()
    args.generator = args.generator.resolve()
    args.out.mkdir(parents=True, exist_ok=True)

    base_env = os.environ.copy()
    base_env.update(
        {
            "GO": args.go,
            "GOOS": args.goos,
            "GOARCH": args.goarch,
            "GOTOOLCHAIN": "local",
            "CGO_ENABLED": "0",
        }
    )
    if args.goamd64:
        base_env["GOAMD64"] = args.goamd64
    runner = shlex.split(args.runner)
    seeds = range(args.first, args.first + args.count)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(
            pool.map(
                lambda seed: one_seed(
                    seed, args=args, base_env=base_env, runner=runner
                ),
                seeds,
            )
        )

    failures = [item for item in results if item["status"] != "ok"]
    report = {
        "go_version": subprocess.run(
            [args.go, "version"], text=True, capture_output=True, check=True
        ).stdout.strip(),
        "goos": args.goos,
        "goarch": args.goarch,
        "goamd64": args.goamd64,
        "first": args.first,
        "count": args.count,
        "functions": args.functions,
        "failures": failures,
    }
    report_path = args.out / "report.json"
    report_path.write_text(json.dumps(report, indent=2) + "\n")
    print(
        f"{args.goos}/{args.goarch}: {len(results) - len(failures)} clean, "
        f"{len(failures)} failed / {len(results)} seeds"
    )
    print(report_path)
    for failure in failures:
        print(f"{failure['status']} seed {failure['seed']}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
