#!/usr/bin/env bash
# Metamorphic fuzz campaigns on foreign architectures, run under qemu user-mode emulation
# (used on GEEKR9 inside `nix shell nixpkgs#go nixpkgs#git nixpkgs#python3 nixpkgs#qemu`).
# 386 runs natively on an amd64 Linux host. 32-bit targets (386, arm, mipsle) exercise the
# decomposition of 64-bit operations (dec64.rules); the others exercise their own lowering rules.
# Usage: cross_campaigns.sh GOTIP_DIR OUT [FIRST_SEED] [SEEDS_PER_RUN]
# EXTRA_FLAGS (environment) is appended to every run's generator flags (e.g. --bits).
# SPECS (environment) overrides the target list: space-separated arch:emulator[:VAR=val,VAR=val],
# e.g. "riscv64:qemu-riscv64:GORISCV64=rva23u64,QEMU_CPU=max ppc64le:qemu-ppc64le:GOPPC64=power10,QEMU_CPU=power10".
set -u
TIP=$1 OUT=$2 S0=${3:-30000} K=${4:-100}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
export JOBS=${JOBS:-12}
run() { # name first toolchain goarch emulator flags [pathprefix]
  local name=$1 a=$2 tc=$3 arch=$4 emu=$5 flags=$6 pre=${7:-}
  env ${vars//,/ } PATH="$pre${pre:+:}$PATH" GOEXEC="$emu" FUZZ_FLAGS="$flags ${EXTRA_FLAGS:-}" nice -n 10 \
    "$here/fuzz_campaign.sh" "$a" $((a+K-1)) 300 "$OUT/$name" "$tc" "$arch" > "$OUT/$name.log" 2>&1
  echo "$name: $(grep -c '^== seed' "$OUT/$name.log") failing seeds, $(grep -c "^== run failed" "$OUT/$name.log") failed runs"
}
i=0
SPECS=${SPECS:-"386: arm:qemu-arm mipsle:qemu-mipsel riscv64:qemu-riscv64 ppc64le:qemu-ppc64le ppc64:qemu-ppc64 s390x:qemu-s390x loong64:qemu-loongarch64 mips64le:qemu-mips64el"}
# Canary: one seed per arch whose first expression is golang/go#82763 (wrong on go1.27.3, all arches).
for spec in $SPECS; do
  IFS=: read -r arch emu vars <<< "$spec"; tag=$arch${vars:+-$(echo "$vars" | tr -c "A-Za-z0-9\n" _ | cut -c1-40)}
  env ${vars//,/ } GOEXEC="$emu" FUZZ_FLAGS="--canary" JOBS=1 "$here/fuzz_campaign.sh" 1 1 20 "$OUT/canary-$tag" go1.27.3 "$arch" > "$OUT/canary-$tag.log" 2>&1
  if grep -q "^== seed" "$OUT/canary-$tag.log"; then echo "canary $tag: detected"; else echo "canary $tag: MISSED"; fi
done
for spec in $SPECS; do
  IFS=: read -r arch emu vars <<< "$spec"; tag=$arch${vars:+-$(echo "$vars" | tr -c "A-Za-z0-9\n" _ | cut -c1-40)}
  run "rel-$tag"        $((S0 + i*4*K))       go1.27.3 "$arch" "$emu" ""
  run "rel-$tag-branchy" $((S0 + (i*4+1)*K)) go1.27.3 "$arch" "$emu" "--branchy"
  run "tip-$tag"        $((S0 + (i*4+2)*K))   local    "$arch" "$emu" ""             "$TIP/bin"
  run "tip-$tag-index"  $((S0 + (i*4+3)*K))   local    "$arch" "$emu" "--index --branchy" "$TIP/bin"
  i=$((i+1))
done
echo ALL-CROSS-DONE
