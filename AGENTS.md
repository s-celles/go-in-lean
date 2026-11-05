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
- ToDo

## Layout

See `README.md` for the directory layout and how to run each harness.
