#!/usr/bin/env bash
# Float/conversion campaigns over many targets (amd64 Linux host, inside
# `nix shell nixpkgs#go nixpkgs#python3 nixpkgs#qemu`): a canary per target (must be detected),
# then K seeds with go1.27.3 and K with Go master. SPECS: arch:emulator[:VAR=val,...].
# Note: a mismatch seen only under qemu may be an emulator FPU bug; confirm with the disassembly.
# Usage: float_cross.sh GOTIP_DIR OUT [FIRST_SEED] [K]
set -u
TIP=$1 OUT=$2 S0=${3:-70000} K=${4:-30}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
export JOBS=${JOBS:-12}
SPECS=${SPECS:-"amd64: amd64::GOAMD64=v3 386: 386::GO386=softfloat arm64:qemu-aarch64 arm:qemu-arm:GOARM=7 arm:qemu-arm:GOARM=5 mipsle:qemu-mipsel mipsle:qemu-mipsel:GOMIPS=softfloat mips64le:qemu-mips64el riscv64:qemu-riscv64 riscv64:qemu-riscv64:GORISCV64=rva23u64,QEMU_CPU=max ppc64le:qemu-ppc64le ppc64le:qemu-ppc64le:GOPPC64=power10,QEMU_CPU=power10 s390x:qemu-s390x loong64:qemu-loongarch64"}
i=0
for spec in $SPECS; do
  IFS=: read -r arch emu vars <<< "$spec"; tag=$arch${vars:+-$(echo "$vars" | tr -c "A-Za-z0-9\n" _ | cut -c1-40)}
  env ${vars//,/ } GOEXEC="$emu" FUZZ_FLAGS="--canary" JOBS=1 "$here/float_campaign.sh" 1 1 20 "$OUT/canary-$tag" go1.27.3 "$arch" > "$OUT/canary-$tag.log" 2>&1
  if grep -q "^== seed" "$OUT/canary-$tag.log"; then echo "canary $tag: detected"; else echo "canary $tag: MISSED"; fi
  for tc in rel tip; do
    if [ "$tc" = tip ]; then a=$((S0 + (2*i+1)*K)); pre="$TIP/bin:"; t=local; else a=$((S0 + 2*i*K)); pre=""; t=go1.27.3; fi
    env ${vars//,/ } PATH="$pre$PATH" GOEXEC="$emu" nice -n 10 "$here/float_campaign.sh" "$a" $((a+K-1)) 120 "$OUT/$tc-$tag" "$t" "$arch" > "$OUT/$tc-$tag.log" 2>&1
    echo "$tc-$tag: $(grep -c '^== seed' "$OUT/$tc-$tag.log") failing seeds, $(grep -c '^== run failed' "$OUT/$tc-$tag.log") failed runs"
  done
  i=$((i+1))
done
echo ALL-FLOAT-DONE
