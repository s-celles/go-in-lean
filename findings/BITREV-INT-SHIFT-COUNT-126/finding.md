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
