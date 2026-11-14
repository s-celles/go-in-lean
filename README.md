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

MIT; Go-derived code retains its BSD 3-Clause notices. See [LICENSE](LICENSE) and [NOTICE](NOTICE).
