#!/usr/bin/env bash
# Metamorphic fuzz campaigns on foreign architectures, run under qemu user-mode emulation
# (used on GEEKR9 inside `nix shell nixpkgs#go nixpkgs#git nixpkgs#python3 nixpkgs#qemu`).
# 386 runs natively on an amd64 Linux host. 32-bit targets (386, arm, mipsle) exercise the
# decomposition of 64-bit operations (dec64.rules); the others exercise their own lowering rules.
# Usage: cross_campaigns.sh GOTIP_DIR OUT [FIRST_SEED] [SEEDS_PER_RUN]
set -u
TIP=$1 OUT=$2 S0=${3:-30000} K=${4:-100}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
export JOBS=${JOBS:-12}
run() { # name first toolchain goarch emulator flags [pathprefix]
  local name=$1 a=$2 tc=$3 arch=$4 emu=$5 flags=$6 pre=${7:-}
  PATH="$pre${pre:+:}$PATH" GOEXEC="$emu" FUZZ_FLAGS="$flags" nice -n 10 \
    "$here/fuzz_campaign.sh" "$a" $((a+K-1)) 300 "$OUT/$name" "$tc" "$arch" > "$OUT/$name.log" 2>&1
  echo "$name: $(grep -c '^== seed' "$OUT/$name.log") failing seeds, $(grep -c "^== run failed" "$OUT/$name.log") failed runs"
}
i=0
SPECS="386: arm:qemu-arm mipsle:qemu-mipsel riscv64:qemu-riscv64 ppc64le:qemu-ppc64le ppc64:qemu-ppc64 s390x:qemu-s390x loong64:qemu-loongarch64 mips64le:qemu-mips64el"
# Canary: one seed per arch whose first expression is golang/go#82763 (wrong on go1.27.3, all arches).
for spec in $SPECS; do
  arch=${spec%%:*} emu=${spec#*:}
  PATH="$PATH" GOEXEC="$emu" FUZZ_FLAGS="--canary" JOBS=1 "$here/fuzz_campaign.sh" 1 1 20 "$OUT/canary-$arch" go1.27.3 "$arch" > "$OUT/canary-$arch.log" 2>&1
  if grep -q "^== seed" "$OUT/canary-$arch.log"; then echo "canary $arch: detected"; else echo "canary $arch: MISSED"; fi
done
for spec in $SPECS; do
  arch=${spec%%:*} emu=${spec#*:}
  run "rel-$arch"        $((S0 + i*4*K))       go1.27.3 "$arch" "$emu" ""
  run "rel-$arch-branchy" $((S0 + (i*4+1)*K)) go1.27.3 "$arch" "$emu" "--branchy"
  run "tip-$arch"        $((S0 + (i*4+2)*K))   local    "$arch" "$emu" ""             "$TIP/bin"
  run "tip-$arch-index"  $((S0 + (i*4+3)*K))   local    "$arch" "$emu" "--index --branchy" "$TIP/bin"
  i=$((i+1))
done
echo ALL-CROSS-DONE
