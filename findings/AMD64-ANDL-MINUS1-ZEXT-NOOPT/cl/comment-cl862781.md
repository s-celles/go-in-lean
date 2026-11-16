<!-- Top-level comment for CL 862781 (golang/go#36897), from the local verification of 2026-11-15. Posted on patchset 5 on 2026-11-16 as written, with no vote. -->

I tested patchset 5 locally (linux/amd64, built with make.bash on top of its parent).

- The reproducer from golang/go#36897 (comment of 2026-11-06), built with -gcflags='-N -l',
  prints 9223372036854775813 with go1.27.4 and 5 with this CL.
- A per-pass translation-validation sweep of 3,000 random integer functions
  (amd64, -N -l, lowered passes) found 8 functions with the #36897 pattern at
  lower on go1.27.4, and none with this CL.

This comes from an independent personal project, and the checking tool is
AI-assisted, so please take it as a data point only.

Assisted by AI.
