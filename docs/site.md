# Documentation and findings website

The site uses Hugo Extended 0.152.2, Hextra v0.13.0 and the shared
[site-kit](https://github.com/s-celles/site-kit) module, pinned at v0.3.0 in
`site/go.mod` and imported before Hextra. The site follows site-kit's SPEC 0.3,
the structure the project sites share: menu order, a home page with the data
stamp, disclaimer, provenance, stat tiles and citation, the Statuses,
Methodology, Upstream, History and Conflict of interest pages, and `llms.txt`. `site-kit.json` at the
repository root declares the SPEC version and the menu. Go and Hugo are the only
build tools; no Node.js, npm or JavaScript build is required. Hextra supplies the
sidebar, system-aware dark mode and local full-text search. site-kit supplies
the badges (a word-to-tone map and display labels in `params.siteKit`), the stat
tiles, the filterable and sortable tables (`tables.js`, complete without
JavaScript), the chart tooltips (`viz.js`), the footer line and validated light
and dark palettes. The goéland brand supplies the header and icon.

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
- `docs/upstream-status.md` holds the hand-written upstream notes: issue and CL
  states with their scope, which the finding pages show. `docs/upstream.tsv` is
  the site-kit upstream snapshot (SPEC §6: repo, number, kind, state, dates,
  `fixes`, `cited_by`, title). `scripts/history.py` generates it from the issues
  and CLs that `docs/upstream-status.md` links, plus the project's own CLs, and
  the Upstream page shows it by repository before the notes. Both are checked-in
  snapshots, not browser-time API queries; refresh them when reviews or merges
  change. A closed issue does not imply every release branch is fixed.
- `docs/history.json` feeds the History page: for each day with commits, the
  number of Lean `theorem`/`lemma` declarations and of registered and proved
  property entries at that day's last commit, plus the opening and closing dates
  of the GitHub issues linked from `docs/upstream-status.md`, and the mailing,
  merge and abandon dates of the project's Go Gerrit CLs. It is a checked-in
  snapshot written by `python3 -I scripts/history.py`, which queries git, the
  GitHub API and Gerrit. `--offline` refreshes only the git part. Re-run it
  when the upstream status changes. Finding counts come from the first date in
  each `findings/*.yaml` history. The charts follow site-kit's markup: inline SVG
  from 0 on one y-axis, one tab stop per chart (`data-viz="dense"`, arrow keys
  step through the days), a legend for two or more series and a data table.
- `CITATION.cff` supplies the home page's Cite section (text and BibTeX).
- `docs/disclosures.tsv` supplies the Conflict of interest page: one row per
  contributor and project (contributor, ORCID, project, kind, role, note), a
  systems by contributors matrix, the use of AI assistants and what limits the
  bias. The one-line summary in `cmd/sitegen/disclosure.go` appears on the home
  page, in `llms.txt`, the footer, the README and `CITATION.cff`; keep it in step
  with the file. The page is at `/conflict-of-interest/`, in the main menu as
  Disclosure after Methodology, as on the other project sites.
- The generator also writes `llms.txt`, `llms-full.txt` (every finding and
  property as text) and `registry.json` (the manifests as JSON) at the site root.
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
kit=$(cd site && go mod download -json github.com/s-celles/site-kit | python3 -c 'import json,sys; print(json.load(sys.stdin)["Dir"])')
python3 -I "$kit/tools/check_site.py" --site site/public --hugo site/hugo.yaml --config site-kit.json --repo .
hugo --source site --minify --destination /tmp/second
python3 -I "$kit/tools/compare_builds.py" site/public /tmp/second --config site-kit.json
```

`check_site.py` checks the built HTML against the SPEC rules (SK-...);
`compare_builds.py` checks that two builds of one commit are identical.
`.github/workflows/site.yml` runs both. It builds and checks pull requests, and deploys pushes
to `main` through GitHub Pages. Repository Pages must use the GitHub Actions
source. The deployment base URL comes from `actions/configure-pages`, allowing
repository subpaths. Generated content is uploaded only as a deployment artifact.

The website's build and generator tests are independent of the formal build
(`.github/workflows/ci.yml`, `scripts/check.sh`).

## Licences

The footer names the licences: code MIT, files derived from Go BSD 3-Clause
(`NOTICE`), data and prose CC BY 4.0 (`LICENSE-DATA`). The project guide's
Licence section lists the paths under each.
