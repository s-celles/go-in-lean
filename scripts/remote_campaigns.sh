#!/usr/bin/env bash
# Fuzz campaigns for a many-core amd64 Linux host (used on GEEKR9 inside
# `nix shell nixpkgs#go nixpkgs#git nixpkgs#python3`). Native amd64, so GOAMD64=v3
# (BMI2 shifts: SHLX/SARX/SHRX) is exercised for real. Results in $OUT/*.log.
# Usage: remote_campaigns.sh GOTIP_DIR OUT [FIRST_SEED]
set -u
TIP=$1 OUT=$2 S0=${3:-10000}
here=$(cd "$(dirname "$0")" && pwd)
mkdir -p "$OUT"
export JOBS=${JOBS:-12}
run() { # name first last toolchain flags goamd64 [pathprefix]
  local name=$1 a=$2 b=$3 tc=$4 flags=$5 v=$6 pre=${7:-}
  PATH="$pre${pre:+:}$PATH" FUZZ_FLAGS="$flags" GOAMD64=$v nice -n 10 \
    "$here/fuzz_campaign.sh" "$a" "$b" 300 "$OUT/$name" "$tc" > "$OUT/$name.log" 2>&1
  echo "$name: $(grep -c '^== seed' "$OUT/$name.log") failing seeds"
}
run rel-v1-plain    $S0         $((S0+199))  go1.27.3 ""                  v1
run rel-v3-plain    $((S0+200)) $((S0+399))  go1.27.3 ""                  v3
run rel-v3-branchy  $((S0+400)) $((S0+599))  go1.27.3 "--branchy"         v3
run rel-v3-index    $((S0+600)) $((S0+799))  go1.27.3 "--index --branchy" v3
run tip-v3-plain    $((S0+800)) $((S0+999))  local    ""                  v3 "$TIP/bin"
run tip-v3-index    $((S0+1000)) $((S0+1199)) local   "--index --branchy" v3 "$TIP/bin"
echo ALL-CAMPAIGNS-DONE
