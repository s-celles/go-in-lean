# Conventions for contributors and coding agents

## Commits

- Use [Conventional Commits](https://www.conventionalcommits.org/):
  `type(scope): summary`, with types `feat`, `fix`, `docs`, `test`, `ci`,
  `refactor`, `chore`. Scopes in use: `conformance`, `harness`, `formal`,
  `ci`, `notes`.
- AI-assisted commits end with the trailer `Assisted-by: AI` — no model or
  tool name, and no `Co-Authored-By` line for the assistant. The same line
  closes pull request descriptions and upstream issues ("Assisted by AI.");
  no "Generated with ..." tool banner anywhere.
- Do not commit or push unless asked.

## Repository rules

- All written artifacts are in English: documentation (`README.md`,
  `docs/`, finding write-ups), commit messages, code comments, and
  upstream artifacts (GitHub issues, Gerrit CLs). Interactive session
  prose may be in another language, but everything committed or posted
  upstream is English.
- Record every notable change in `CHANGELOG.md`
  ([Keep a Changelog](https://keepachangelog.com/en/1.1.0/)), under
  `[Unreleased]` until a version is tagged, in the same commit as the change.
  Versions follow [Semantic Versioning](https://semver.org/).

## Findings and evidence

- Deduplicate before creating a finding. Search existing local findings and
  issues, the upstream issue tracker, and relevant Gerrit CLs by operation,
  symptom and suspected mechanism. Record the queries, dates and matching
  references in the finding's research record. Reuse an existing finding for
  another manifestation of the same root cause instead of opening a duplicate.
- Keep one finding ID, one `findings/<ID>/` evidence directory and one
  `findings/<ID>.yaml` manifest per finding. Include a concise explanation,
  expected and observed behaviour, source citations, a minimal standalone
  reproducer where possible, and the commands and outputs needed to repeat it.
  Keep generated website pages out of commits.
- A failed proof or model counterexample alone is never a Go bug. Check the
  model, documented preconditions and reachability, then reproduce on the
  affected Go toolchain before using `go_discrepancy_reproduced`. Record exact
  versions or commits, GOOS/GOARCH, CPU settings, build flags and emulator use.
  Check the pinned toolchain, current release and Go tip when relevant; state
  explicitly which configurations were tested, unaffected or not checked.
- Use the existing manifest statuses and record dated history with evidence.
  Keep proof/reproduction classification separate from human-review,
  publication and upstream merge states. Record current issue and CL states in
  `docs/upstream-status.md`; an issue closing or a master CL merging does not
  establish that release branches contain the fix. Do not override a human's
  classification or disclosure decision; document new evidence for review.
- In this repository's reports and documentation, use full upstream URLs or
  qualified references such as `golang/go#82782`, not ambiguous bare issue
  numbers. Go CL commit messages may use Go's `Fixes #<N>` convention.

## Upstream publication and scope

- Read-only research in upstream source, documentation, issues and Gerrit is
  allowed as part of the task. Preparing local reproducers, patches and draft
  responses does not authorize publishing them.
- Publishing an upstream issue, comment, PR or Gerrit patchset requires human
  review of the proposed content and an explicit user instruction to publish.
  An existing authorization remains valid for the reviewed finding or follow-up
  within its stated scope. Permission to publish does not itself grant permission
  to merge a change or change unrelated upstream state.
- For Go compiler fixes, follow `docs/upstream-cls.md`: report bugs on GitHub,
  send code changes through Gerrit, and keep patches out of issue bodies.
  A finding is not a commitment to implement or maintain its fix. Present this
  work as an independent personal project, never as an official Go project report.
- If an external write is outside the authorized scope, leave a concrete,
  reviewable local result and explain what remains. Continue authorized local
  work and read-only research; do not interpret this rule as a ban on reading
  external sources.

## Privacy and memory safety

- Public artifacts must not expose credentials, private repository URLs,
  private working-tree paths, machine/account details or unrelated personal
  data. Retain legitimate authorship and relevant public source attribution.
- Keep potentially memory-unsafe findings in a private working tree outside
  this public repository. Do not include their details in public files, issues,
  comments, commits or website content before human triage. This includes
  suspected out-of-bounds memory access, uninitialized-memory exposure, type
  confusion and process crashes outside an explicit unsafe contract.
- Tell the person running the agent and let them decide on private reporting
  through the affected project's security process. Publish only after human
  confirmation that coordinated disclosure permits it or that the behaviour
  was already public upstream, with a reference to that public evidence.
  Recoverable Go panics and compiler build failures alone do not establish
  memory unsafety.

## Layout

See `docs/project.md` for the directory layout and how to run each harness.
`README.md` is a short entry point to the documentation website.
