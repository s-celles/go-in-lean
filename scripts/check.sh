#!/usr/bin/env bash
# End-to-end check: everything CI runs, in order. No network or AI services
# are needed beyond what `lake`/`go` fetch for themselves (nothing: the Lean
# project has no dependencies and the Go module has none).
set -euo pipefail
cd "$(dirname "$0")/.."

step() { printf '\n\033[1m== %s\033[0m\n' "$*"; }

step "0. toolchain versions"
lake env lean --version   # the toolchain pinned by lean-toolchain, whatever `lean` is on PATH
lake --version
go version
echo "expected Go: $(cat go/.go-version)"
[ "$(go env GOVERSION)" = "$(cat go/.go-version)" ] || echo "WARNING: Go toolchain differs from the pinned version; results are about the pinned version only"

step "1. source scan: banned proof shortcuts"
# sorry/admit bypass the kernel; native_decide / decide +native / ofReduceBool
# would be indistinguishable from bv_decide in the axiom audit.
if grep -rnE '\b(sorry|admit|native_decide)\b|decide \+native|ofReduceBool|Lean\.reduceBool' \
     --include='*.lean' GoInLean GoInLean.lean | grep -v '^GoInLean/Audit.lean' | grep -vE '^[^:]+:[0-9]+:\s*--' ; then
  echo "banned token found in accepted proof sources"; exit 1
fi
echo "ok"

step "2. generated files are up to date with the pinned Go sources"
python3 -I scripts/gen_bits_tables.py --check
python3 -I scripts/rules_to_lean.py --check
python3 -I scripts/arm64_shift_rules.py --check

step "3. lake build (all models, specs and proofs)"
lake build

step "4. axiom audit"
lake exe audit

step "5. Go vet + tests (property oracles on the real standard library)"
( cd go && go vet ./... && go test ./... )

step "6. differential vectors: Go implementation vs Lean model"
mkdir -p build
( cd go && go run ./tests/vectors ) > build/bits_vectors.json
lake exe checkvectors build/bits_vectors.json

step "6b. slices with aliasing: bounded exhaustive model-vs-spec search, then Go-vs-model replay"
lake exe slicesearch 8
( cd go && go run ./tests/vectors_slices 5 ) > build/slices_vectors.json
lake exe checkslices build/slices_vectors.json

step "7. manifest validation (ids, theorem names, Go tests, statuses)"
lake exe audit --json > build/audit.json
python3 -I scripts/validate_manifest.py targets/properties.yaml build/audit.json

step "8. mutation test: deliberately wrong models must be refuted and reproduced in Go"
python3 -I scripts/mutation_test.py

echo
echo "ALL CHECKS PASSED"
