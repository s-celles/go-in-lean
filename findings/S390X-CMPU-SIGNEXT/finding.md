# S390X-CMPU-SIGNEXT: `uint64(int8(-128)) < 0xFFFFFFFF` is true on s390x (reachable since Go 1.26)

**Classification:** `go_discrepancy_reproduced`. **Potentially novel compiler miscompilation.**
**Severity:** medium for s390x: wrong comparison result for a widened negative small integer
against a constant close to 2^32. Only `GOARCH=s390x` is affected.
**Security:** a wrong unsigned comparison can matter for range checks written by hand; no
evident exploitable path (bounds checks use `IsInBounds` on full-width values). Handled as a
private report until reviewed.
**Human review status:** reviewed and approved by the maintainer of this repository on 2026-11-02; reported upstream as [golang/go#82774](https://github.com/golang/go/issues/82774).

## Summary

`S390X.rules` ("Convert 64-bit comparisons to 32-bit comparisons", same text in go1.25.5,
go1.27.3 and master `babb75be`):

```
(CM(P|P|PU|PU)const x:(MOV(H|HZ|H|HZ)reg _) [c]) => (CMP(W|W|WU|WU)const x [c])
(CM(P|P|PU|PU)const x:(MOV(B|BZ|B|BZ)reg _) [c]) => (CMP(W|W|WU|WU)const x [c])
```

The alternatives expand in lockstep; the instance `(CMPUconst x:(MOV(H|B)reg _) [c]) =>
(CMPWUconst x [c])` is wrong. `CMPUconst` compares the 64-bit register with the zero-extended
immediate; a negative sign-extended value is ≥ 2^64 − 2^15 and never below it, but its low 32
bits (≥ 2^32 − 2^15) can be below or equal to an immediate close to 2^32 (e.g. 0xFFFFFFFF).
The other three instances (signed compare, or zero-extended value) are sound.

In go1.25.5 the argument was passed on the stack and read with a sign-extending load, so
`MOVBreg` disappeared and the rule did not match. Since go1.26 (register-based arguments on
s390x) the `MOVBreg` stays and the rule fires: assembly `MOVB R2, R0; CMPWU R0, $4294967295`.

Fix (`fix.patch`, against master `babb75be`): keep the three sound instances, and narrow the
unsigned compare of a sign-extended value only when the immediate is below 2^31 (`c >= 0`).

## Reproducer

```go
//go:noinline
func f(y int8) bool { return uint64(y) < 0xFFFFFFFF }
// GOARCH=s390x: f(-128) == true. Spec: uint64(int8(-128)) == 0xFFFFFFFFFFFFFF80, not < 0xFFFFFFFF.
// Also uint64(int16(-20)) <= 0xFFFFFFF0 is true (spec false). Equality is not affected.
```

## Versions tested (2026-11-02, qemu-s390x 11.1.2)

| Toolchain | Result |
|---|---|
| go1.22.12 .. go1.25.5 | correct (rule present but not reached) |
| go1.26.10, go1.27.3 | **wrong** |
| master `babb75be` | **wrong** |
| master `babb75be` + `fix.patch` | correct |

Controls: amd64, riscv64 correct. With the fix on master, `go test -short
cmd/compile/internal/ssa cmd/compile/internal/test` and `go test -count=1 cmd/internal/testdir
-run 'Test/codegen|Test/fixedbugs'` pass.

## Lean model (`property.lean` = `GoInLean/Compiler/S390XCompare.lean`)

* `cmpu_movbreg_refuted`, `cmpu_movhreg_refuted`: kernel-checked counterexamples.
* `cmpu_movhreg_fixed`, `cmpu_movbreg_fixed`: sound when the immediate is below 2^31.
* The other instances (`cmp_movhreg_sound`, `cmp_movhzreg_sound`, `cmpu_movhzreg_sound`, the
  byte versions and the word rule) are sound for every immediate.

## How it was found

`scripts/cross_campaigns.sh`, seed 41665 (master, s390x, `--index --branchy`): the
constant-count version indexed a different table entry; the branch condition
`uint64(y) < uint64(4294967295)` with `y int8 = -128` was taken.

## Known-issue search (2026-11-02)

GitHub search on golang/go ("s390x CMPWU", "s390x comparison sign extension 1.26",
"s390x miscompile"): no match (golang/go#72018 and #81928 are unrelated).
