# SSA-COMPOSE-CONST64-TYPE: tip miscompiles `(x >> c) >> d` for narrow signed x and huge counts

**Classification:** `go_discrepancy_reproduced`, **regression on master only** (go1.28-devel
`babb75be`, 2026-11-01). Released toolchains (go1.25.5, go1.27.3) are correct.
**Severity:** low–medium (silent wrong code; needs a constant combined shift count ≥ 2^32 on
an int8/16/32 value; reachable through inlining like SSA-SHIFTMASK-SIGNED-COUNT).
**Human review status:** approved 2026-11-02; reported upstream as [golang/go#82767](https://github.com/golang/go/issues/82767).

## Reproducer

```go
//go:noinline
func f(y int32) int32 { return (y >> 1) >> (1 << 62) }
// tip: f(2) == 1, f(-5) == -3.  Spec (and go1.27.3): 0 and -1.
```

Extent (`(y op 1) op K`, all widths/kinds, K ∈ {1<<62, 1<<32, 1<<16, 1<<8, 256}):
30 mismatches on tip (arm64 and amd64), 0 on go1.27.3. Only signed right shifts of
int16/int32 (other kinds are folded to 0 first).

## Root cause (two cooperating defects)

1. `_gen/generic.rules:537-549` (master), the shift-composition rules, e.g.
   `(Rsh32x64 <t> (Rsh32x64 x (Const64 [c])) (Const64 [d])) && !uaddOvf(c,d) => (Rsh32x64 x (Const64 <t> [c+d]))`,
   give the combined count the type `<t>` of the *shifted value* (int32), not a 64-bit type.
   This is the same defect class as golang/go#81868 (fixed by CL 795240 for the
   shift-canonicalisation rules only); these nine rules were not changed. Present in go1.27.3
   too, where it was harmless.
2. On master, `ssa.InitLimit` ends with
   `lim.PropagateUnsignedSignedRelationship(uint(v.Type.Size()) * 8)`; for this Const64 typed
   int32 it truncates 2^62+1 to 32 bits (= 1), the count's limit becomes [1,1], and
   `ssacompile/prove.go:2454` marks the shift bounded (`v.AuxInt = 1`). The lowered machine
   shift then masks the count: `y >> ((2^62+1) & 31)` = `y >> 1`.

SSA (`GOSSAFUNC=f+`): after `opt` `v7 = Const64 <int32> [4611686018427387905]`,
`v11 = Rsh32x64 <int32> [false] v6 v7`; after `prove` the flag is `[true]`.
go1.27.3 leaves it `[false]`.

## How it was found

`scripts/metamorphic_fuzz.py` (constant vs run-time-argument vs inlined versions of random
integer expressions): 200 seeds on go1.27.3 → 0 mismatches; 200 seeds on tip → 7 failing
seeds (303 320 343 437 451 457 470), all explained by this defect (all clean with the fix).

## Fix (validated on master, not submitted)

`fix.patch`: use `Const64 <typ.UInt64>` for the combined count in the nine 8/16/32-bit rules
(as CL 795240 did for the canonicalisation rules). On tip: reproducers correct, 30 → 0
mismatches, the 7 fuzz seeds clean, `go test cmd/compile/internal/ssa cmd/compile/internal/test`
and `cmd/internal/testdir -run Test/codegen/shift.go` pass. Making `InitLimit` robust
(e.g. using the op's own width for Const64) would be a complementary hardening.

## Reproduction

```sh
cd go && go test -tags reproduce_findings ./reproducers -run ComposeConst64 -v   # with gotip
```
