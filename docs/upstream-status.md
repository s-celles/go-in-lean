# Upstream issue, PR and CL status

Last checked: **2026-11-05**, from the GitHub issue API and the Go Gerrit API.

This is the single status table for upstream bugs found, reproduced, or
directly followed by go-in-lean. GitHub and Gerrit are separate workflows: an
issue or PR may remain open after a CL is merged, and a closed issue is not by
itself evidence that every release branch contains the fix.

Gerrit uses `NEW` for a CL that is still in review, `MERGED` for a submitted
change, and `ABANDONED` for one that will not be submitted. The notes
distinguish a complete fix from a partial or related CL.

| Upstream item | Item state | CL | CL state | Scope / note |
|---|---|---|---|---|
| [#54255](https://github.com/golang/go/issues/54255) | CLOSED | none | — | `math/bits.Add64` without its carry precondition; closed as working as intended, not a compiler bug. |
| [PR #80355](https://github.com/golang/go/pull/80355) | OPEN, not merged | [799281](https://go-review.googlesource.com/c/go/+/799281) | NEW | Original emulated `MulAdd` fix. |
| [PR #80355](https://github.com/golang/go/pull/80355) | OPEN, not merged | [858921](https://go-review.googlesource.com/c/go/+/858921) | NEW | Complete correctly-rounded fix, including the midway bridge and float32 case found here. |
| [#80577](https://github.com/golang/go/issues/80577) | OPEN | [65290](https://go-review.googlesource.com/c/go/+/65290), [568616](https://go-review.googlesource.com/c/go/+/568616) | MERGED | Historical sign/zero-extension rule fixes; neither establishes the spill/restore contract. |
| [#80577](https://github.com/golang/go/issues/80577) | OPEN | [806340](https://go-review.googlesource.com/c/go/+/806340) | MERGED | RISC-V-specific fix only. |
| [#80577](https://github.com/golang/go/issues/80577) | OPEN | [810440](https://go-review.googlesource.com/c/go/+/810440), [810460](https://go-review.googlesource.com/c/go/+/810460), [810441](https://go-review.googlesource.com/c/go/+/810441) | MERGED | CL 806340 backports for Go 1.25, 1.26 and 1.27. |
| [#80577](https://github.com/golang/go/issues/80577) | OPEN | [823424](https://go-review.googlesource.com/c/go/+/823424) | NEW | ARM64 redundant sub-word extension elision; still in review. |
| [#80577](https://github.com/golang/go/issues/80577) | OPEN | [825904](https://go-review.googlesource.com/c/go/+/825904) | NEW | Central spill/restore contract, patchset 6. It does not yet guard the ARM64/PPC64 double-extension rules exercised by `spill_restore_fuzz.py`. |
| [#80577](https://github.com/golang/go/issues/80577) | OPEN | [827284](https://go-review.googlesource.com/c/go/+/827284) | ABANDONED | Earlier contract change, folded into CL 825904. |
| [#82763](https://github.com/golang/go/issues/82763) | OPEN | [857741](https://go-review.googlesource.com/c/go/+/857741) | NEW | Signed comparison of huge constant shift counts. |
| [#82767](https://github.com/golang/go/issues/82767) | OPEN | [857342](https://go-review.googlesource.com/c/go/+/857342) | NEW | Correct type for combined shift counts; also fixes the `prove/Limit` ICE family. Rediscovered on tip by the alternative-compiler campaign (2026-11-05); comment posted that go1.27.3/go1.26.10 show no wrong code for the backports #82810/#82811. |
| [#82772](https://github.com/golang/go/issues/82772) | CLOSED | [857442](https://go-review.googlesource.com/c/go/+/857442) | MERGED | MIPS `Rsh8` sign-extension bit; merged 2026-11-05 as `ff3d7c172b6b` after showing the mipsle/mips64le crypto tryjob failures were pre-existing (identical `.text` with and without the fix; #82681). |
| [#82773](https://github.com/golang/go/issues/82773) | OPEN (REOPENED) | [857143](https://go-review.googlesource.com/c/go/+/857143) | MERGED | RISC-V fix. The issue was reopened on 2026-11-05 because the bug also affects Loong64. |
| [#82773](https://github.com/golang/go/issues/82773) | OPEN (REOPENED) | [859601](https://go-review.googlesource.com/c/go/+/859601), [859721](https://go-review.googlesource.com/c/go/+/859721) | NEW | Two Loong64 fixes currently in review. |
| [#82774](https://github.com/golang/go/issues/82774) | CLOSED | [856905](https://go-review.googlesource.com/c/go/+/856905) | MERGED | S390X unsigned comparison of a sign-extended value. |
| [#82774](https://github.com/golang/go/issues/82774) | CLOSED | [859762](https://go-review.googlesource.com/c/go/+/859762), [859742](https://go-review.googlesource.com/c/go/+/859742) | NEW | Go 1.26 and 1.27 backports. |
| [#82775](https://github.com/golang/go/issues/82775) | OPEN | [857742](https://go-review.googlesource.com/c/go/+/857742) | NEW | PPC64 `Type.Size()` byte/bit mismatch. |
| [#82776](https://github.com/golang/go/issues/82776) | CLOSED | [857343](https://go-review.googlesource.com/c/go/+/857343) | MERGED | Full-width MIPS constant shift count. |
| [#82776](https://github.com/golang/go/issues/82776) | CLOSED | [859662](https://go-review.googlesource.com/c/go/+/859662), [859801](https://go-review.googlesource.com/c/go/+/859801) | NEW | Go 1.26 and 1.27 backports. |
| [#82777](https://github.com/golang/go/issues/82777) | CLOSED | [857344](https://go-review.googlesource.com/c/go/+/857344) | MERGED | ARM64 constant-flag `CSINV`. |
| [#82777](https://github.com/golang/go/issues/82777) | CLOSED | [859761](https://go-review.googlesource.com/c/go/+/859761), [859781](https://go-review.googlesource.com/c/go/+/859781) | NEW | Go 1.26 and 1.27 backports. |
| [#82782](https://github.com/golang/go/issues/82782) | OPEN | [857542](https://go-review.googlesource.com/c/go/+/857542) | NEW | Power10 `ReverseBytes16` result type. |
| [#82786](https://github.com/golang/go/issues/82786) | OPEN | [857821](https://go-review.googlesource.com/c/go/+/857821) | NEW | ARM `MVNshiftRA` constant fold. |
| [#82825](https://github.com/golang/go/issues/82825) | CLOSED | [858262](https://go-review.googlesource.com/c/go/+/858262) | MERGED | x86 SBB carry masks now clobber flags. |
| [#82825](https://github.com/golang/go/issues/82825) | CLOSED | [859802](https://go-review.googlesource.com/c/go/+/859802), [859663](https://go-review.googlesource.com/c/go/+/859663) | NEW | Go 1.26 and 1.27 backports. |
| [#82834](https://github.com/golang/go/issues/82834) | OPEN | [857821](https://go-review.googlesource.com/c/go/+/857821) | NEW | `bits.Sub64` is another manifestation of #82786; no separate fix. |
| [#82839](https://github.com/golang/go/issues/82839) | OPEN | [858581](https://go-review.googlesource.com/c/go/+/858581) | NEW | `prove` fact carried through a narrowing extension. |
| [#82847](https://github.com/golang/go/issues/82847) | OPEN | [858901](https://go-review.googlesource.com/c/go/+/858901) | NEW | Missing immediate on masked SIMD shifts. |
| [#82873](https://github.com/golang/go/issues/82873) | CLOSED (no backport) | none (fixed on master by [731300](https://go-review.googlesource.com/c/go/+/731300)) | MERGED (master only) | go1.26 arm64/loong64: `bits.Reverse*` intrinsics typed `int`, so a shift by their result raises a spurious `negative shift amount` panic; filed 2026-11-05 from `s-celles-bot` asking whether a 1.26 backport is warranted (`findings/BITREV-INT-SHIFT-COUNT-126`). Second manifestation found the same day: `prove` derives an empty range from `Com8(BitRev8 <int>)` and turns a guarded modulo into an unconditional divide panic (`reproducer-prove.go`; posted as a [comment](https://github.com/golang/go/issues/82873#issuecomment-6677261173) on 2026-11-06, after the issue had been closed). Closed 2026-11-06 by a maintainer: no backport warranted, since the bug is unlikely to be hit and results in a panic, not corruption; the prove variant is also a panic, so the reasoning stands and no follow-up is planned. |

## Other upstream blockers exercised by campaigns

| Issue | State | CL tracked here | Note |
|---|---|---|---|
| [#82745](https://github.com/golang/go/issues/82745) | OPEN | none | Existing SIMD assembler failure; not a go-in-lean finding. |
| [#81842](https://github.com/golang/go/issues/81842) | CLOSED | [841125](https://go-review.googlesource.com/c/go/+/841125) (master only) | ppc64x `DIVD`/`DIVW` clobber CR0: 6 spurious `integer divide by zero` panics in the ppc64le cross campaign on go1.26.10/go1.27.3; fix bisected to `6200ca7253`; backport suggestion posted 2026-11-05 from `s-celles-bot`. Not a go-in-lean finding. |

## Related external PRs

| Project | PR | State | Note |
|---|---|---|---|
| Yaegi | [traefik/yaegi#1750](https://github.com/traefik/yaegi/issues/1750) (issue) | OPEN | Shift count converted to the operand type in assignments; see `upstream-bugs.md`. |
| Yaegi | [traefik/yaegi#1751](https://github.com/traefik/yaegi/issues/1751) (issue) | OPEN | A negative shift count does not panic; filed 2026-11-06 from `s-celles-bot`; see `upstream-bugs.md`. |
| Gobra | [#960](https://github.com/viperproject/gobra/pull/960) | CLOSED, draft, not merged | Earlier overflow-checking implementation. |
| Gobra | [#1015](https://github.com/viperproject/gobra/pull/1015) | OPEN, draft, not merged | Replacement bounded-integer encoding referenced by the prior-art review. |

## Context CLs referenced by root-cause analysis

| CL | State | Why it is referenced |
|---|---|---|
| [621357](https://go-review.googlesource.com/c/go/+/621357) | MERGED | Introduced the shift arithmetic optimization analyzed for #82763. |
| [795240](https://go-review.googlesource.com/c/go/+/795240) | MERGED | Earlier generic-rule type fix related to #82767. |
| [804220](https://go-review.googlesource.com/c/go/+/804220) | MERGED | Earlier `prove` fact-propagation change related to #82839. |

When an entry changes, update both its state and the date at the top. Detailed
before/after validation remains in [`cl-verification.md`](cl-verification.md)
and in the corresponding `findings/` directory.
