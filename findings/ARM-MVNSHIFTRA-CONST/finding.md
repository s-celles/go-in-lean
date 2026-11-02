# ARM-MVNSHIFTRA-CONST: ARM constant folding of `MVNshiftRA` drops the complement

**Classification:** `go_discrepancy_reproduced`. **Compiler miscompilation (wrong code).**
**Impact:** silent wrong results on `GOARCH=arm` when an `MVNshiftRA` (bitwise NOT of an
arithmetic right shift) gets a constant operand during lowering, e.g. `bits.TrailingZeros64(0)`
evaluates to 32 instead of 64. No security impact.
**Affected:** `GOARCH=arm`, go1.16 .. go1.27.3 and master `a0c8470e`. go1.15 and earlier are correct
(regression from the conversion of ARM.rules to typed AuxInts in go1.16).
**Human review status:** pending. Not reported upstream.

## Summary

`src/cmd/compile/internal/ssa/_gen/ARM.rules` (master line 1067):

```
(MVNshiftLL (MOVWconst [c]) [d]) => (MOVWconst [^(c<<uint64(d))])
(MVNshiftRL (MOVWconst [c]) [d]) => (MOVWconst [^int32(uint32(c)>>uint64(d))])
(MVNshiftRA (MOVWconst [c]) [d]) => (MOVWconst [int32(c)>>uint64(d)])
```

The RA rule omits the `^`. go1.15 had `(MOVWconst [^int64(int32(c)>>uint64(d))])`; the complement
was lost when the rules moved from `->` to typed `=>` in go1.16. A scan of every
`<op>shift(LL|RL|RA) (MOVWconst [c]) [d]` constant fold in ARM.rules finds no other inconsistency.

Trigger: the 32-bit decomposition of `Ctz64` computes
`Ctz32(lo) + (^Zeromask(lo) & Ctz32(hi))`; on ARM `Zeromask` lowers to `SRAconst [31]` and the
following `Com32` merges into `MVNshiftRA [31]`. If the low word folds to a constant only during
`lower` (for instance `bits.OnesCount16` of a constant is a table load there), the rule fires on
`MVNshiftRA [31] (MOVWconst [0])` and yields 0 instead of -1, dropping the high half:

```
rewriting v10 = MVNshiftRA <uint32> [31] v5   ->  v10 = MOVWconst <uint32> [0]     (should be -1)
rewriting v12 = ANDconst <uint32> [32] v10    ->  v12 = MOVWconst <uint32> [0]
rewriting v32 = ADD <uint32> v17 v12          ->  v32 = Copy v17                   (32, not 64)
```

Fix (`fix.patch`, against master `a0c8470e`): `(MOVWconst [^(c>>uint64(d))])`.

## Reproducer

```go
//go:noinline
func f() int { return bits.TrailingZeros64(uint64(uint16(bits.OnesCount16(16384))) &^ 16777217) }
// GOARCH=arm: f() == 32. Spec: the argument is 0, so 64.
```

## Versions tested (2026-11-02, qemu-arm 11.1.2)

| Toolchain | arm |
|---|---|
| go1.26.10, go1.27.3 | **wrong (32)** |
| master `a0c8470e` | **wrong** |
| master `a0c8470e` + `fix.patch` | correct (64) |

Rule text: correct in go1.12 .. go1.15, wrong from go1.16. Controls: 386 and mipsle correct
(their lowering has no MVN-with-shift ops). With the fix on master: `go test -short
cmd/compile/internal/ssa cmd/compile/internal/test` and `go test -count=1 cmd/internal/testdir
-run Test/codegen` pass.

## Lean model (`property.lean` = `GoInLean/Compiler/ARMMvnShift.lean`)

* `fold_refuted`, `fold_unsound`: kernel-checked counterexample (`c = 0, d = 31`: fold 0, instruction -1).
* `fold_fixed`: the fold with the complement equals the instruction for every constant and count.
* `fold_always_wrong`: without the complement the fold never matches the instruction.
* `ctz64_zero_needs_complement`: the 32-bit `Ctz64` decomposition gives 64 with the complement, 32 without.

## How it was found

Index-mode `--bits` campaign on master (`scripts/cross_campaigns.sh`, arm, seed 60372): the constant
version indexed `tab255[32]`, the run-time version `tab255[64]`. Reduced from the fuzz program, then
the `lower` rewrite trace (`-d=ssa/lower/debug=3`) pointed at the fold.

## Known-issue search (2026-11-02)

GitHub search on golang/go ("ARM MVNshiftRA", "arm TrailingZeros64 wrong 32", "arm 32-bit constant
folding MVN shift"): no match.
