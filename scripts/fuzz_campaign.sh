#!/usr/bin/env bash
# Run metamorphic_fuzz.py over a range of seeds with a given toolchain; print each mismatching
# expression's source. Usage: fuzz_campaign.sh FIRST LAST N OUTDIR [GOTOOLCHAIN] [GOARCH]
# Environment: JOBS (parallelism, default 6), FUZZ_FLAGS (--branchy, --index, --canary), GOAMD64.
set -u
FIRST=$1 LAST=$2 N=$3 OUT=$4 TC=${5:-go1.27.3} ARCH=${6:-}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
run() {
  s=$1; d="$OUT/s$s"
  GOTOOLCHAIN=$TC python3 -I "$here/metamorphic_fuzz.py" "$s" "$N" "$d" ${FUZZ_FLAGS:-} >/dev/null 2>&1 || { echo "seed $s: generator failed"; return; }
  res=$(cd "$d" && GOTOOLCHAIN=$TC GOARCH=$ARCH go run . 2>&1)
  if echo "$res" | grep -q "mismatches" && ! echo "$res" | grep -q " 0 mismatches"; then
    echo "== seed $s ($TC ${ARCH:-native})"
    echo "$res" | grep "^expr" | head -6
    for i in $(echo "$res" | grep -o "^expr [0-9]*" | awk '{print $2}' | sort -u); do grep "^func c$i(" "$d/main.go"; done
  fi
}
export -f run; export OUT N TC ARCH here FUZZ_FLAGS
seq "$FIRST" "$LAST" | xargs -P "${JOBS:-6}" -I{} bash -c 'run {}'
echo "campaign $FIRST..$LAST done"
