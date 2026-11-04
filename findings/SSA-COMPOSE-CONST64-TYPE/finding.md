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

## Addendum (2026-11-02): modest counts suffice for int8 / int16

The combined count is truncated to the width of the *shifted* type, so for int8 any pair of
constant counts whose sum is a multiple of 256 (plus a small remainder) misbehaves:

```go
func shr8(y int8, a, b uint) int8 { return (y >> a) >> b }
// master: shr8(100, 128, 128) == 100, shr8(100, 100, 157) == 50, shr8(-7, 128, 128) == -7
// spec / go1.27.3: 0, 0, -1.   int16: (100 >> 40000) >> 25537 == 50 on master (spec 0).
```

A second fuzzing campaign (200 seeds, master, GOARCH=amd64 under Rosetta) found 8 failing
seeds, all of them fixed by `fix.patch` (e.g. `(x >> 256) >> 256` on int8).

## Addendum (2026-11-04): the same defect can crash the compiler

Tip at discovery `672197524bb0` panics in `ssacompile.(*factsTable).flowLimit` at
`prove.go:1518` while compiling this smaller boundary case (`ice_reproducer.go`):

```go
func f(y int32) int32 {
	return (y >> 1) >> (uint32(1) << 31)
}
```

The first shift is necessary: without it there is no shift-composition rewrite and no ICE.
An unknown `uint32` parameter also stays clean; a local or direct constant triggers the crash.
An unsigned `y` stays clean because the generic large-shift rule folds it to zero before the
composition rule can manufacture the mistyped count.

With `prove` disabled, the post-`opt` SSA is:

```text
v5  = Const64 <int32> [2147483649]
v13 = Rsh32x64 <int32> [false] y v5
```

`InitLimit` first records the exact positive `Const64`, then propagates its relationship using
the erroneous `int32` type. Intersecting `2147483649` with its 32-bit signed interpretation
`-2147483647` yields an unsatisfiable limit with `Min=2147483649` and `Max=-2147483647`.
`flowLimit` checks only `b.Min >= 0` and then evaluates `a.Min >> b.Max`, causing Go's own
`negative shift amount` panic.

This is another consequence of #82767, not a separate root cause. Patchset 1 of CL 857342,
applied unchanged on top of `672197524bb0`, makes the reproducer compile and passes
`cmd/compile/internal/ssa` and `cmd/compile/internal/test`. A separate defensive
`!b.Unsat()` check would prevent the panic, but would not repair the mistyped SSA value.

### Boundary matrix

`scripts/prove_limit_fuzz.py` compiles each case separately so one ICE cannot hide later
boundaries. On the same commit `672197524bb0`, its 330 two- and three-shift cases give:

| Toolchain | ICE | Clean | Other errors |
|---|---:|---:|---:|
| pristine tip | 60 | 270 | 0 |
| tip + CL 857342 patchset 1 | 0 | 330 | 0 |
| current master `ede4e4ff00` (2026-11-04) | 60 | 270 | 0 |

All 60 crashes are signed arithmetic right shifts of `int8`, `int16`, or `int32` whose
combined count falls in a negative signed residue window for the value width. The left-shift
and unsigned-right-shift controls remain clean. Three-stage compositions double the number
of reproducers but reach the same `flowLimit` panic and the same mistyped-`Const64` root; no
second defect was found. An audit of the host-language shifts and divisions in `prove.go`
also found no other directly panicable operation beyond the two right-shift cases at the
incomplete `b.Min >= 0` guard.

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
# Compile-only ICE boundary on an unpatched tip:
gotip tool compile findings/SSA-COMPOSE-CONST64-TYPE/ice_reproducer.go
```
