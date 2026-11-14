# Documentation and findings website

The site uses Hugo Extended 0.152.2 and Hextra v0.13.0. Go and Hugo are the
only build tools; Hextra ships its browser assets. No Node.js, npm or JavaScript
build is required. Hextra supplies the sidebar, system-aware dark mode and
local full-text search. Finding and property registries also have a browser-local
row filter and sortable columns; the complete tables remain available without JavaScript. The existing goéland brand supplies the header and icon.

## Build and preview

From the repository root, with Go and the pinned Hugo binary on PATH:

```sh
go run ./cmd/sitegen
hugo --source site --minify
hugo server --source site
```

`nix develop` includes the same pinned Hugo release used by the Pages workflow.
The nested `go/` module and its dependency-free conformance harness are unchanged
by the website's separate root module (`gopkg.in/yaml.v3` is its only dependency).

## Source data

- `targets/properties.yaml` defines every registered property. Status counts
  refer to entries, not audited theorems. A property may reference several theorems.
- `findings/*.yaml` defines each finding's title, priority, classification,
  affected toolchains, architecture, source records, reproducer, Lean evidence,
  upstream URLs and dated history. Detailed Markdown/JSON research records stay
  alongside the evidence and are linked from the generated pages.
- `docs/upstream-status.md` supplies issue and CL states. These are a checked-in
  snapshot, not a browser-time API query; update that record when reviews or
  merges change. A closed issue does not imply every release branch is fixed.
- `docs/project.md` holds the full project guide, including the material moved
  from the former long README, and supplies the site's pitch. The README is a
  short entry point to the published site. The research docs, upstream bug notes and
  changelog are imported on every build. Relative links are rewritten to site
  pages where available, otherwise to their exact repository paths.

The generator rejects malformed or multi-document YAML, unknown fields/statuses,
invalid histories, duplicate IDs, missing evidence, unresolved theorem/test
references and findings missing from the YAML registry. It validates and renders
everything before replacing an existing generated directory. An existing output
must carry its `.sitegen` marker so handwritten directories are never deleted.

`site/content/` is generated, ignored and never committed. Edit YAML, original
docs, templates or CSS, then regenerate. Output ordering is stable and no build
timestamp is added. Stale pages disappear when source entries are removed.

## Trust and reporting

The `kernel` tier records kernel-checked proof evidence without a per-theorem
native-evaluation axiom. `bv_decide` additionally trusts the native-evaluation
axiom for its generated certificate. A trust badge is not a property status;
unresolved entries can still record a trust tier for their supporting evidence.
No model counterexample is automatically labelled a Go defect.

Finding priorities are project triage labels, not upstream security ratings.
P0 denotes critical impact, P1 wrong results on ordinary inputs, P2 edge cases
or build failures, and P3 controls, latent rules or negligible impact.

## Checks and deployment

```sh
go test ./cmd/sitegen
go run ./cmd/sitegen
hugo --source site --minify
```

`.github/workflows/site.yml` builds and checks pull requests, and deploys pushes
to `main` through GitHub Pages. Repository Pages must use the GitHub Actions
source. The deployment base URL comes from `actions/configure-pages`, allowing
repository subpaths. Generated content is uploaded only as a deployment artifact.

The website's build and generator tests are independent of the formal build.
During the 2026-11-14 validation, the site build, registry checks, browser checks,
Nix package, and Go tests/vet passed. The full `scripts/check.sh` run reached
the Lean build, then timed out in the unchanged `mul_sound_16` and
`ctz_sound_64` proofs in `GoInLean/Compiler/ProveLimits.lean`; an isolated
retry reproduced both timeouts. That run does not establish a successful
end-to-end axiom audit or differential/mutation check.
