<h1>
  <picture>
    <source media="(prefers-color-scheme: dark)" srcset="assets/brand/lockup-dark.svg">
    <img alt="go-in-lean" src="assets/brand/lockup.svg" height="56">
  </picture>
</h1>

Finding correctness bugs in Go with bit-precise Lean 4 models and executable reproducers.
A model counterexample is only reported as a Go bug after reproduction and human review.

**[Documentation & findings](https://s-celles.github.io/go-in-lean/)** ·
[Property registry](https://s-celles.github.io/go-in-lean/properties/) ·
[Upstream status](https://s-celles.github.io/go-in-lean/upstream/)

The [project guide](https://s-celles.github.io/go-in-lean/docs/project/) covers
setup, results, the research map, repository layout and contributing.

## Run the checks

```sh
nix develop
scripts/check.sh
```

See the [quick start](https://s-celles.github.io/go-in-lean/docs/project/#quick-start)
for prerequisites and commands outside Nix, and [AGENTS.md](AGENTS.md) for contributor conventions.

## Disclosure

The author reports issues and contributes fixes to Go, and has reported issues to
Yaegi, as part of this project; has no funding, employment or other interest tied to
the systems examined; and works with an AI assistant. See the
[disclosures page](https://s-celles.github.io/go-in-lean/disclosures/) and
[docs/disclosures.tsv](docs/disclosures.tsv).

## Licence

Code: MIT ([LICENSE](LICENSE)); files derived from Go keep the BSD 3-Clause
licence of the Go Authors ([NOTICE](NOTICE)). Data and prose (documentation,
findings, registry, snapshots, site content): CC BY 4.0
([LICENSE-DATA](LICENSE-DATA)). The paths under each licence are listed in the
[project guide](https://s-celles.github.io/go-in-lean/docs/project/#licence).
To cite go-in-lean, see [CITATION.cff](CITATION.cff).
