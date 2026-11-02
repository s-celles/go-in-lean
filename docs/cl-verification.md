# CL verification (2026-11-02)

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
