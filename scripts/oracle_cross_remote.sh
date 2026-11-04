#!/usr/bin/env bash
# Runs one emitted cross-arch canary directory (exprs.json + gomain/ +
# expected.txt produced by oracle_canaries.py) against the toolchain under
# qemu. The Lean oracle is architecture-independent, so the expected output
# is computed locally and compared here.
# Usage: oracle_cross_remote.sh DIR GOARCH GOEXEC [VAR=val ...]
set -u
d=$1; arch=$2; emu=$3; shift 3
cd "$d/gomain"
GOARCH=$arch go build -o prog . || { echo "BUILD FAILED"; exit 2; }
$emu ./prog > ../actual.txt 2>&1
if cmp -s ../expected.txt ../actual.txt; then
  echo "CLEAN (toolchain agrees with the spec)"
else
  echo "CAUGHT"
  paste -d'|' ../expected.txt ../actual.txt | awk -F'|' '$1 != $2' | head -4
fi
