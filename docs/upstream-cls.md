# Sending the fixes upstream (Gerrit)

The Go project reviews changes on Gerrit (go-review.googlesource.com), not through GitHub pull
requests, and asks that patches not be pasted into issues (thepudds on golang/go#82763,
2026-11-02). Each finding under `findings/<ID>/` that has a fix carries a ready-to-mail package in
`findings/<ID>/cl/`:

* `issue<N>.go` — a `// run` regression test for `test/fixedbugs/` (fails before the fix, passes after);
* `message.txt` — the commit message (`cmd/compile: ...` + body + `Fixes #<N>.`);
* `fix.patch` (in the finding dir) — the compiler change, including the regenerated `rewrite*.go`.

Verification per CL (before/after on pristine master, foreign arches under qemu) is in
`docs/cl-verification.md`.

## Prerequisite (once)

Contributing code to Go requires a signed Google CLA under your identity. Follow
https://go.dev/doc/contribute: create a Google account at go-review, agree to the CLA, and install
the review tool: `go install golang.org/x/review/git-codereview@latest`.

## Per change

```
cd $GOROOT_SRC_CHECKOUT            # a fresh clone of go.googlesource.com/go
git checkout -b fix-<N> origin/master
git apply /path/to/findings/<ID>/fix.patch
cp /path/to/findings/<ID>/cl/issue<N>.go test/fixedbugs/
# sanity: the test must pass with the patched toolchain on the affected GOARCH
#   (e.g. GOOS=linux GOARCH=mipsle go run -exec qemu-mipsel test/fixedbugs/issue<N>.go)
git add -A
git commit -F /path/to/findings/<ID>/cl/message.txt
git codereview change            # amends with a Change-Id
git codereview mail              # sends to Gerrit for review
```

Do not run `git codereview mail` from this automation: it posts under your Gerrit identity and
depends on your CLA. The automation only prepares and verifies the packages.

## Notes

* The generated `rewrite*.go` files in each `fix.patch` are what `go generate` produces for the
  rule change; reviewers expect both the `_gen/*.rules` edit and the regenerated file in one CL.
* `findings/PPC64-POWER10-BSWAP16-BCE` is **not** here: it is a potential security issue, kept in
  the private repository and submitted through the Go security process, not Gerrit directly.
