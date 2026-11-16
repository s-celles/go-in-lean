# CL verification (2026-11-02)

Current review and merge states are kept in
[`upstream-status.md`](upstream-status.md); this file records the validation
performed for each change.

Each fix was verified on a pristine Go master (`babb75be`) on an amd64 Linux host, rebuilding
`cmd/compile` and running the finding's `test/fixedbugs` regression test for the affected GOARCH
(foreign arches under qemu-user 11.1.2). "before" is the unpatched compiler, "after" is with the
finding's `fix.patch`. rc is the test process exit code (0 = pass; the test panics on a wrong
result).

| Issue | GOARCH | before | after | fix.patch files |
|---|---|---|---|---|
| #82763 | amd64 | fail | pass | generic.rules + rewritegeneric.go |
| #82767 | amd64 | fail | pass | generic.rules + rewritegeneric.go |
| #82772 | mipsle | fail | pass | MIPS.rules + rewriteMIPS.go |
| #82773 | riscv64 | fail | pass | RISCV64.rules + rewriteRISCV64.go |
| #82774 | s390x | fail | pass | S390X.rules + rewriteS390X.go |
| #82775 | ppc64le | fail | pass | PPC64.rules + rewritePPC64.go |
| #82776 | mipsle | fail | pass | MIPS.rules + rewriteMIPS.go |
| #82777 | arm64 | fail | pass | ARM64.rules + rewriteARM64.go |

With all eight patches applied together on master: `go test -short cmd/compile/internal/ssa
cmd/compile/internal/test` and `go test -count=1 cmd/internal/testdir -run Test/codegen` pass.

Each `fix.patch` includes both the `_gen/*.rules` edit and the regenerated `rewrite*.go`, as a Go
CL is expected to. The ready-to-mail package per finding is in `findings/<ID>/cl/` (regression
test + commit message); see `docs/upstream-cls.md` for the Gerrit workflow.

## Gerrit CLs (mailed 2026-11-02)

| Issue | CL |
|---|---|
| #82763 | https://go-review.googlesource.com/c/go/+/857741 |
| #82767 | https://go-review.googlesource.com/c/go/+/857342 |
| #82772 | https://go-review.googlesource.com/c/go/+/857442 |
| #82773 | https://go-review.googlesource.com/c/go/+/857143 |
| #82774 | https://go-review.googlesource.com/c/go/+/856905 |
| #82775 | https://go-review.googlesource.com/c/go/+/857742 |
| #82776 | https://go-review.googlesource.com/c/go/+/857343 |
| #82777 | https://go-review.googlesource.com/c/go/+/857344 |
| #82825 | https://go-review.googlesource.com/c/go/+/858262 |

## #82782 (migrated from private, 2026-11-02)

`GOPPC64=power10`, test/fixedbugs/issue82782.go: before fix rc=2 (f=7), after fix rc=0. Reclassified from a suspected OOB to a wrong-code miscompilation after canary + `go tool objdump` showed no out-of-bounds access. CL https://go-review.googlesource.com/c/go/+/857542 (mailed 2026-11-02).

### Direct-test review follow-up (validated 2026-11-13, published 2026-11-14)

Robert Griesemer requested a more direct test of `bits.ReverseBytes16`.
The updated `cl/issue82782.go` adds a `//go:noinline` wrapper that returns
`bits.ReverseBytes16(x)` directly, then checks all 65,536 `uint16` inputs
against `uint16(x<<8 | x>>8)` computed with a `uint32` loop variable. The
original conditional-selection reproducer is retained: the direct return
already works before the fix, while that reproducer detects the incorrect
type's effect on `prove`. Disassembly confirms the direct wrapper uses
`BRH` on Power10.

Validation used a fresh build of CL 857542 patchset 2 (`1e9d2862fe18`),
with qemu-user 11.0.1 for both PPC64 byte orders. For the before-fix control,
the compiler was rebuilt from the same sources with only the intrinsic's
`TUINT16` change reverted to `TUINT`.

| Target | Before fix | With fix |
|---|---|---|
| ppc64le, power10 | rc=2, original reproducer returns 7 instead of -5 | pass |
| ppc64, power10 | rc=2, original reproducer returns 7 instead of -5 | pass |
| ppc64le, power9 | pass | pass |
| ppc64, power9 | pass | pass |
| amd64 | — | pass |

Go 1.27.4 independently gives the same PPC64 results as the before-fix
control. The PS2 toolchain also passes `go test math/bits -run
'^TestReverseBytes$' -count=1`. The updated regression test passes through
the official `cmd/internal/testdir` harness on both PPC64 byte orders:

```sh
GOPPC64=power10 CGO_ENABLED=0 go test cmd/internal/testdir \
  -run '^Test/fixedbugs/issue82782.go$' -count=1 -target=linux/ppc64le
GOPPC64=power10 CGO_ENABLED=0 go test cmd/internal/testdir \
  -run '^Test/fixedbugs/issue82782.go$' -count=1 -target=linux/ppc64
```

These cross-target harness runs use `go_linux_ppc64le_exec` and
`go_linux_ppc64_exec` wrappers on `PATH`, each invoking the corresponding
qemu-user emulator with `-cpu power10`.

The incremental patch against PS2 is
[`update-ps2.patch`](../findings/PPC64-POWER10-BSWAP16-MISCOMPILE/cl/update-ps2.patch);
the posted reply is
[`review-reply.md`](../findings/PPC64-POWER10-BSWAP16-MISCOMPILE/cl/review-reply.md).
Published as patchset 3 (`ab447517908b`) on 2026-11-14. The reply was
posted on the original review thread and the direct-test request resolved.

## #82786 (ARM MVNshiftRA fold, 2026-11-02)

`GOARCH=arm`, test/fixedbugs/issue82786.go: before fix `TrailingZeros64(0) = 32`, after fix 64 (qemu-arm). CL https://go-review.googlesource.com/c/go/+/857821.

## AMD64-SBB-CARRYMASK-FLAGS (2026-11-03, master `2b74366d`)

| Finding | GOARCH | before | after | fix.patch files |
|---|---|---|---|---|
| SBB carrymask clobberFlags | amd64 | fail | pass | `_gen/AMD64Ops.go` + `_gen/386Ops.go` + regenerated `ssaop/opGen.go` |
| (same) | 386 | pass | pass | master's shift-lowering rework removed the 386 shape; the annotation fix keeps it fixed |

"before" on pristine master `2b74366d`: the regression test's amd64 parts are wrong
(`lshEq(1,65)`=1, `lshNe(1,65)`=0, `rshU(1,65)`=1, `rshS(-1,65)`=0, `lsh32(1,33)`=1), recorded
before patching the same checkout; "after" is with `fix.patch` (rebuilt, `go generate`
included). With the patch: `go test -short cmd/compile/internal/ssa
cmd/compile/internal/ssacompile cmd/compile/internal/test`, `go test cmd/internal/testdir
-run 'Test/prove|Test/loopbce|Test/checkbce|Test/codegen'` and `-run Test/fixedbugs` pass.
The regression test, commit message and issue number are in
`findings/AMD64-SBB-CARRYMASK-FLAGS/cl/` (golang/go#82825).

Patchset 2 of CL 858262 (2026-11-03, same Change-Id `Ia4e6b506`): the regression test gains
`rshLe16` (int16, `<=`) and `rshGt64` (int64, `>`), both failing on go1.27.3 and passing on
master+patch (amd64 and 386); commit message extended to state that all four comparison
operators share the width mask's flags. Pushed from the Linux workstation (its own Gerrit
credentials).

## PROVE-EXT-CONST-TRUNC / golang/go#82839 (2026-11-03)

Fix re-validated on master `740d909b` (the 2026-11-02 validation was against `2885c994`):
`fix.patch` applies cleanly (one file, `ssacompile/prove.go`, +22/−2), the reproducer goes from
`sink=1` (wrong) to `sink=0` (spec), the regression test `issue82839.go` panics on go1.27.3 and
passes on master+patch, and the `ssa`/`ssacompile`/`test` (short) plus
`prove|loopbce|checkbce|codegen|fixedbugs` suites pass. Mailed as Gerrit CL
https://go-review.googlesource.com/c/go/+/858581 (mailed from the Linux workstation).

### Patchset 2 following review (prepared 2026-11-15, uploaded 2026-11-16)

Keith Randall preferred moving the check to where the constant is truncated
(option (b) in the 2026-11-13 reply). The extension case in
`factsTable.update` is now unchanged. The `x+delta > w` constant case runs
only when `w` fits in `x`'s type, checked by a new helper `fitsSigned`. Its
doc comment says only what it does, and the reason sits at the call site.
The commit subject becomes "do not truncate a wider constant in prove's
x+delta case" (`cl/message-ps2.txt`).

Validated on the parent of PS1 (`740d909bb5`) with the same regression
test `issue82839.go`. It panics with go1.27.4 and passes with PS2. Also passing
with PS2: `test/prove*.go`, `loopbce`, `checkbce`, all of `codegen` and
`fixedbugs` through `cmd/internal/testdir`, and `go test -short`
`cmd/compile/internal/ssa` and `cmd/compile/internal/ssacompile`. Files:
`fix-ps2.patch` (compiler change against the base), `cl/update-ps1-to-ps2.patch`
(incremental), and `cl/review-reply-ps2.md` (draft replies). Nothing has been
uploaded or posted.

## CL 862781 (golang/go#36897, by Keith Randall, verified locally 2026-11-15)

Patchset 5 (`230a349655`, parent CL 833045 `abec217787`), built with `make.bash`.

- `findings/AMD64-ANDL-MINUS1-ZEXT-NOOPT/reproducer.go` with `-gcflags='-N -l'`:
  go1.27.4 prints `9223372036854775813`, the CL prints `5`.
- `ssa_tv.py check --funcs f --goarch amd64 --lowered --gcflags "-N -l"`:
  one equivalence failure at `lower` on go1.27.4, none with the CL.
- `ssa_tv.py gen --suite ext --seed 20261115 --count 300 --goarch amd64 --lowered
  --gcflags "-N -l"` (3,000 functions): 8 reports on go1.27.4, all at `lower` with
  the #36897 signature; 0 with the CL.

Nothing has been posted on the CL.
