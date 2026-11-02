#!/usr/bin/env bash
# Run float_fuzz.py over a range of seeds with one toolchain/target; print each mismatching seed.
# Usage: float_campaign.sh FIRST LAST N OUTDIR [GOTOOLCHAIN] [GOARCH]
# Environment: JOBS (default 6), GOEXEC (emulator for a foreign GOARCH), FUZZ_FLAGS, GO* variables.
set -u
FIRST=$1 LAST=$2 N=$3 OUT=$4 TC=${5:-go1.27.3} ARCH=${6:-}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
run() {
  s=$1; d="$OUT/s$s"
  GOTOOLCHAIN=$TC GOARCH=$ARCH python3 -I "$here/float_fuzz.py" "$s" "$N" "$d" ${FUZZ_FLAGS:-} >/dev/null 2>&1 \
    || { echo "== run failed: seed $s: generator failed"; return; }
  res=$(cd "$d" && GOTOOLCHAIN=$TC GOARCH=$ARCH go run ${GOEXEC:+-exec "$GOEXEC"} . 2>&1)
  if ! echo "$res" | grep -q "mismatches"; then
    echo "== run failed: seed $s ($TC ${ARCH:-native}): $(echo "$res" | head -2 | tr '\n' ' ' | cut -c1-200)"
  elif ! echo "$res" | grep -q " 0 mismatches"; then
    echo "== seed $s ($TC ${ARCH:-native})"
    echo "$res" | grep "^expr" | head -6
    for i in $(echo "$res" | grep -o "^expr [0-9]*" | awk '{print $2}' | sort -un | head -4); do grep "^func v$i(" "$d/main.go" | cut -c1-400; done
  fi
}
export -f run; export OUT N TC ARCH here FUZZ_FLAGS GOEXEC
seq "$FIRST" "$LAST" | xargs -P "${JOBS:-6}" -I{} bash -c 'run {}'
echo "float campaign $FIRST..$LAST done"
