# PROVE-EXT-CONST-TRUNC: prove truncates a wide constant after looking through an extension

**Classification:** `go_discrepancy_reproduced`. **Compiler miscompilation (wrong code), all
architectures.** Plain safe Go code takes a branch that cannot be taken.
**Impact:** silent wrong results on every GOARCH, including amd64 and arm64. No out-of-bounds access
was demonstrated: the mechanism makes prove declare a branch impossible, so it forces or deletes
branches (wrong values), as in the reproducer.
**Affected:** go1.26.6 .. go1.26.10, go1.27.3 and master `2885c994` for the reproducer below; other
shapes already from go1.24.13 / go1.25.5 (see Versions). go1.26.5 and earlier are correct for it.
**Human review status:** reviewed and filed as golang/go#82839 on 2026-11-03 (maintainer approval); fix re-validated on master 740d909b (reproducer, ssa/ssacompile/test short, prove|loopbce|checkbce|codegen|fixedbugs all pass).

## Reproducer

```go
var sink int

//go:noinline
func f(x uint8) {
	if int32(int16(x)-513) < -536870911 { // int16(x)-513 is in [-513, -258]: always false
		sink = 1
	}
}
// f(0) sets sink = 1 (go1.26.6+, go1.27.3, master; amd64, arm64, ...).
```

## Cause

`cmd/compile/internal/ssacompile/prove.go`, `factsTable.update`:

1. "Look through value-preserving extensions" (master lines 870-888): a fact `ext(x) op w` is
   repeated on the narrow `x` with the **same** `w`, here `SignExt16to32(v65) >= Const32 [-536870911]`
   becomes `v65 >= Const32 [-536870911]` for the 16-bit `v65 = Add16 v64 (Const16 [-513])`.
2. "Process: x+delta > w (with delta constant)" (lines 806-840) then computes `min = w - delta`
   "using integers of the correct size", i.e. `int16(w.AuxInt) - int16(delta)` for a 16-bit `x`.
   `int16(-536870911)` is 1, so it derives `v64 >= 514`, contradicting `v64 <= 255`, and prove
   concludes the branch `>=` is impossible (`-d=ssa/prove/debug=2`: `x+d >= w; x:v64 delta:-513
   w:-536870911`, then `Proved Less32`).

The look-through is only valid when the constant is representable in the narrow type; otherwise the
fact on `x` is trivially true or false and is already decided by the limits of `ext(x)`.

Fix (`fix.patch`, against master `2885c994`): carry the fact through the extension only if the
other operand, when it is a constant, fits in the narrow type (`constFitsIn`). With the fix the
reproducer and the fuzz case are correct, and `go test -short cmd/compile/internal/ssa
cmd/compile/internal/ssacompile cmd/compile/internal/test`, `go test -count=1 cmd/internal/testdir
-run 'Test/prove|Test/loopbce|Test/checkbce'`, `-run Test/codegen` and `-run Test/fixedbugs` pass
(no `Proved` expectation of the prove tests is lost).

## Versions (2026-11-02)

| Toolchain | reproducer above | `if int32(int16(x)-513) < int32(u) { return 1 }` |
|---|---|---|
| go1.21.13 .. go1.24.0 | correct | correct (1.24.0) |
| go1.24.13, go1.25.5 | correct | **wrong** |
| go1.26.0 .. go1.26.5 | correct | **wrong** (1.26.x) |
| go1.26.6, go1.26.10, go1.27.3, master | **wrong** | correct (masked) |
| master + `fix.patch` | correct | correct |

The truncating code and the look-through are textually identical from go1.24 to master; which
shapes reach them changed with other prove work, notably go1.26.6's backport of "fix time
traveling proofs in prove" (`52e5e2f22a`, CL 804220, golang/go#80619), which interleaves fact
learning and simplification per value and exposes the defect for the reproducer above.

## Lean model (`property.lean` = `GoInLean/Compiler/ProveExtDelta.lean`)

* `unguarded_refuted` (kernel): the 32-bit fact holds, the 16-bit derived bound does not.
* `fits_iff`: if the constant fits in 16 bits, the 32-bit and 16-bit facts are equivalent (the
  condition the fix checks).
* `xdelta_sound`: prove's "x+delta >= w" derivation is sound at the narrow width.

## How it was found

`--late --bits` index campaign (constants injected as read-only loads) on arm, seed 90587; the run
on a master carrying all ten earlier fixes isolated it. `-d=ssa/prove/debug=2` showed the bad
derivation; it then reproduced natively on arm64 and amd64.

## Known-issue search (2026-11-02)

No golang/go issue for prove truncating a constant after an extension (searched "prove sign
extension constant", "prove x+delta truncate", "isCleanExt"); golang/go#79874 (slicemask) is a
different prove defect.
