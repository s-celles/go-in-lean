# BITREV-INT-SHIFT-COUNT-126: spurious "negative shift amount" panic on go1.26 arm64/loong64

**Classification:** `go_discrepancy_reproduced`. **Compiler bug (spurious run-time panic),
GOARCH=arm64 and GOARCH=loong64, go1.26 only.** A shift whose count is the result of
`math/bits.Reverse64` (or `Reverse`) panics with `runtime error: negative shift amount`
when the reversed value has its top bit set, although the count is unsigned. No wrong
value is computed; the program aborts.
**Affected:** go1.26.10 on arm64 and loong64. go1.27.3 and master `56ae71df05` are correct;
amd64, ppc64le, riscv64, s390x, arm and mipsle are correct on go1.26.10 (no `Reverse`
intrinsic there).
**Human review status:** reviewed and filed as
[golang/go#82873](https://github.com/golang/go/issues/82873) on 2026-11-05
(from the `s-celles-bot` account), asking whether a 1.26 backport is warranted.
Closed on 2026-11-06 without a backport (fixed on master; judged unlikely to be hit,
and a panic rather than corruption). The prove variant below was posted as a comment
just after the closure; it is also a panic, so it does not change that reasoning.

## Reproducer

`reproducer.go` (cross-compiled, run under qemu-user):

```
GOOS=linux GOARCH=arm64 go1.26.10 build reproducer.go && qemu-aarch64 ./reproducer
panic: runtime error: negative shift amount        # want: 0 0
```

## Root cause

In go1.26 `ssagen/intrinsics.go`, the `math/bits` `Reverse`, `Reverse8/16/32/64`
intrinsics (registered for `sys.ARM64, sys.Loong64`) create their result with type
`types.Types[types.TINT]`. `ssagen` decides whether a shift needs the `0 <= count` check
from the SSA type of the count, so it inserts a `runtime.panicshift` call
(`TBNZ $63, R1` on arm64) for a count of Go type `uint64`.

Commit `819c53c25f` (CL 731300, "cmd/compile: ensure ops have the expected argument
widths", go1.27) changes those result types to `TUINT64`/`TUINT` and removes the check;
its message says the mismatch was not believed to be triggerable. It was not backported to
go1.26.

## How it was found

Cross-architecture run of `scripts/alt_compiler_diff.py` (`bits` suite, seed 20261105,
case `bits-20261105-00090`, linux/arm64 under qemu): gc go1.26.10 was the only toolchain
to fail (`run_error`); go1.27.3, tip, gc go1.27.3 with `-N -l` and TinyGo agreed with the
Lean oracle. The generated count was
`bits.Reverse64(bits.RotateLeft64(7, 63))`, i.e. `0xC000000000000001`.

## Second manifestation: `prove` turns a reachable modulo into an unconditional divide panic

Found on 2026-11-05 by the long cross-architecture campaign (`bits` suite, seed 20261110,
case `bits-20261110-00182`, linux/arm64 and linux/loong64): gc go1.26.10 was the only
toolchain to fail, with `runtime error: integer divide by zero` although the divisor was
guarded to be non-zero.

`reproducer-prove.go`:

```
GOOS=linux GOARCH=arm64 go1.26.10 build reproducer-prove.go && qemu-aarch64 ./reproducer-prove
panic: runtime error: integer divide by zero        # want: 85
```

The divisor is 85; the function body compiles to a lone `CALL runtime.panicdivide`. Same
result on loong64; amd64 prints 85 (no `Reverse8` intrinsic). go1.27.3 and master print 85.

**Mechanism.** `BitRev8` is created with type `int`, so `prove` starts it with the full
64-bit range. `Com8` of it goes through `limit.com(8)`, which truncates the bounds
`[MinInt64, MaxInt64]` to `int8` and complements them, giving the empty signed range
`[0, -1]`. `prove` treats the empty range as a contradiction, i.e. the block as
unreachable, and with `-d=ssa/prove/debug=2` reports `Disproved Neq8` for the
divide-by-zero check `y != 0`: the non-panicking branch is removed. (The same debug flag
also makes go1.26.10 crash with a nil dereference in `removeBranch`.) The trigger is
shape-sensitive: replacing `bits.RotateLeft8(x, 7)` by `x`, `x>>1` or `x+1` hides it, and
no silent wrong-value variant was found in a short search.

**Confirmation.** A go1.26.10 toolchain rebuilt with only the five `BitRev*` result types
in `ssagen/intrinsics.go` changed from `TINT` to `TUINT64/32/16/8`/`TUINT` (the part of
CL 731300 that matters here) prints 85 on arm64 and loong64, and the original campaign
program then agrees with the Lean oracle.

This strengthens the case for a go1.26 backport: besides the spurious shift panic, the
mistyped intrinsic lets `prove` delete reachable code.
