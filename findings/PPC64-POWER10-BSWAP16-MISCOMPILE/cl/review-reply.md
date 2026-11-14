<!-- Posted 2026-11-14 on Robert Griesemer's direct-test request on CL 857542; patchset 3. -->

Added a separate `//go:noinline` wrapper that returns `bits.ReverseBytes16(x)`
directly, and a check of all 65,536 uint16 inputs against the byte-swap formula
computed in uint32 arithmetic. On Power10 the wrapper compiles to `BRH`.

I kept the original reproducer as well: a direct return is already correct
before the fix; the conditional-selection case exposes the incorrect type's
effect on `prove`.

Verified on both ppc64le and ppc64 under qemu, with Power10 and Power9. With
PS2's compiler fix reverted, the test completes the direct checks and then
fails the original case on Power10 (7 instead of -5); with the fix, it passes.
Power9 passes in both cases, as does native amd64 with the fix.

Assisted by AI.
