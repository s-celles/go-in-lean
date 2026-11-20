package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"os"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
)

func TestRegistryCoverageAndDeterminism(t *testing.T) {
	root, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	g := &generator{root: root, pages: map[string][]byte{}, routes: map[string]string{}}
	if err := g.load(); err != nil {
		t.Fatal(err)
	}
	if err := g.render(); err != nil {
		t.Fatal(err)
	}
	for _, p := range g.properties {
		path := "properties/" + slug(p.Package) + "/" + slug(p.ID) + ".md"
		if len(g.pages[path]) == 0 {
			t.Errorf("missing %s", path)
		}
	}
	for _, f := range g.findings {
		path := "findings/" + slug(f.ID) + ".md"
		if len(g.pages[path]) == 0 {
			t.Errorf("missing %s", path)
		}
	}
	counts := map[string]int{}
	for _, p := range g.properties {
		counts[p.Status]++
	}
	if !bytes.Contains(g.pages["_index.md"], []byte(`{{< stat value="`+strconv.Itoa(len(g.properties))+`" label="Registered properties"`)) {
		t.Error("dashboard registered count differs from YAML")
	}
	for status, count := range counts {
		if !bytes.Contains(g.pages["_index.md"], []byte(badge("status", status)+" | "+strconv.Itoa(count)+" |")) {
			t.Errorf("dashboard count differs for %s", status)
		}
	}
	g2 := &generator{root: root, pages: map[string][]byte{}, routes: map[string]string{}}
	if err := g2.load(); err != nil {
		t.Fatal(err)
	}
	if err := g2.render(); err != nil {
		t.Fatal(err)
	}
	if len(g.pages) != len(g2.pages) {
		t.Fatal("page count is not deterministic")
	}
	for path, body := range g.pages {
		if !bytes.Equal(body, g2.pages[path]) {
			t.Errorf("nondeterministic page %s", path)
		}
	}
	upstream := string(g.pages["upstream/_index.md"])
	for _, r := range g.upstream {
		if !strings.Contains(upstream, r.State) {
			t.Errorf("missing upstream state %s", r.State)
		}
		for _, url := range urlRE.FindAllString(r.Item, -1) {
			if !strings.Contains(upstream, url) {
				t.Errorf("missing upstream item %s", url)
			}
		}
	}
}

func TestFullProjectGuideWithMinimalReadme(t *testing.T) {
	root := t.TempDir()
	guide := `# Project guide

**Finding correctness bugs in Go with Lean.**

The complete project introduction.

> **About the name.** A seagull.

## Research map

` + "```mermaid\nflowchart LR\n    Model --> Reproducer\n```\n" + `
## Quick start

Run the full harness.

## Contributing

The complete upstream contribution policy.

## Licence

The complete licence notes.
`
	files := map[string]string{
		"README.md":               "# go-in-lean\n\n[Read the documentation](https://s-celles.github.io/go-in-lean/).\n",
		"docs/project.md":         guide,
		"docs/prior-art.md":       "# Prior art\n",
		"docs/fuzzing-vision.md":  "# Fuzzing vision\n",
		"docs/cedar-notes.md":     "# Research notes\n",
		"upstream-bugs.md":        "# Upstream bugs\n",
		"CHANGELOG.md":            "# Changelog\n",
		"docs/site.md":            "# Building the site\n",
		"docs/upstream-status.md": "# Upstream status\n",
		"docs/disclosures.tsv":    disclosuresSample,
		"CITATION.cff":            "cff-version: 1.2.0\nmessage: Cite it.\ntitle: go-in-lean\nauthors:\n  - family-names: Celles\n    given-names: Sébastien\n",
	}
	for path, body := range files {
		path = filepath.Join(root, path)
		if err := os.MkdirAll(filepath.Dir(path), 0755); err != nil {
			t.Fatal(err)
		}
		if err := os.WriteFile(path, []byte(body), 0644); err != nil {
			t.Fatal(err)
		}
	}
	g := &generator{root: root, pages: map[string][]byte{}, routes: map[string]string{}}
	if err := g.render(); err != nil {
		t.Fatal(err)
	}
	page := string(g.pages["docs/project.md"])
	if !strings.Contains(page, removeTitle(guide)) {
		t.Fatal("project guide was truncated instead of imported in full")
	}
	if !strings.Contains(string(g.pages["_index.md"]), "The complete project introduction.") {
		t.Fatal("home pitch is not read from the project guide")
	}
	for _, path := range []string{"_index.md", "docs/_index.md"} {
		if !strings.Contains(string(g.pages[path]), `relref "/docs/project"`) {
			t.Errorf("project guide is not linked from %s", path)
		}
	}
	got := rewriteLinks("[Research](../README.md#research-map)", "docs/prior-art.md")
	if !strings.Contains(got, `relref "/docs/project" >}}#research-map`) {
		t.Fatalf("former README section link is not preserved: %s", got)
	}
}

func TestRejectMalformedYAML(t *testing.T) {
	for _, input := range []string{"properties: [", "properties: []\nunknown: 1\n", "properties: []\n---\nproperties: []\n", "properties: []\nproperties: []\n"} {
		t.Run(input, func(t *testing.T) {
			path := filepath.Join(t.TempDir(), "manifest.yaml")
			if err := os.WriteFile(path, []byte(input), 0644); err != nil {
				t.Fatal(err)
			}
			var dst struct {
				Properties []Property `yaml:"properties"`
			}
			if err := decodeYAML(path, &dst); err == nil {
				t.Fatal("accepted malformed YAML")
			}
		})
	}
}

func TestRejectStatusesAndHistories(t *testing.T) {
	for _, tc := range []struct {
		status  string
		history []History
	}{
		{"proven", []History{{Date: "2026-11-01", Status: "proved_in_model"}}},
		{"proved_in_model", []History{{Date: "2026-11-01", Status: "proven"}}},
		{"proved_in_model", []History{{Date: "yesterday", Status: "proved_in_model"}}},
		{"proved_in_model", []History{{Date: "2026-11-02", Status: "proved_in_model"}, {Date: "2026-11-01", Status: "proved_in_model"}}},
		{"proved_in_model", []History{{Date: "2026-11-01", Status: "inconclusive"}}},
	} {
		if err := validHistory("EXAMPLE", tc.status, tc.history); err == nil {
			t.Errorf("accepted invalid history %+v", tc)
		}
	}
}

func TestUpstreamPipes(t *testing.T) {
	s := "| [#1](https://github.com/golang/go/issues/1) | OPEN | [2](https://go-review.googlesource.com/c/go/+/2) | NEW | `x | y` and a \\| b |"
	rows, err := parseUpstream(s)
	if err != nil {
		t.Fatal(err)
	}
	if len(rows) != 1 || rows[0].State != "OPEN" || rows[0].CLState != "NEW" || !strings.Contains(rows[0].Note, "`x | y`") {
		t.Fatalf("bad table parse: %+v", rows)
	}
}

func TestGeneratedDirectorySafetyAndStalePages(t *testing.T) {
	out := filepath.Join(t.TempDir(), "content")
	if err := os.Mkdir(out, 0755); err != nil {
		t.Fatal(err)
	}
	if err := os.WriteFile(filepath.Join(out, "handwritten.md"), []byte("keep"), 0644); err != nil {
		t.Fatal(err)
	}
	if err := writePages(out, map[string][]byte{"new.md": []byte("new")}); err == nil {
		t.Fatal("replaced handwritten directory")
	}
	if err := os.WriteFile(filepath.Join(out, ".sitegen"), nil, 0644); err != nil {
		t.Fatal(err)
	}
	if err := writePages(out, map[string][]byte{"new.md": []byte("new")}); err != nil {
		t.Fatal(err)
	}
	if _, err := os.Stat(filepath.Join(out, "handwritten.md")); !os.IsNotExist(err) {
		t.Fatal("stale output survives")
	}
}

func TestImportedLinkRewriting(t *testing.T) {
	in := "[status](upstream-status.md#fixes) [source](../go/tests/bits_test.go) [external](https://go.dev/doc)"
	out := rewriteLinks(in, "docs/prior-art.md")
	if !strings.Contains(out, `[status]({{< relref "/upstream" >}}#fixes)`) {
		t.Fatal(out)
	}
	if !strings.Contains(out, repository+"/blob/main/go/tests/bits_test.go") {
		t.Fatal(out)
	}
	if !strings.Contains(out, "https://go.dev/doc") {
		t.Fatal(out)
	}
}

func TestHistoryPage(t *testing.T) {
	root, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	g := &generator{root: root, pages: map[string][]byte{}, routes: map[string]string{}}
	if err := g.load(); err != nil {
		t.Fatal(err)
	}
	if err := g.render(); err != nil {
		t.Fatal(err)
	}
	page := string(g.pages["history/_index.md"])
	if page == "" {
		t.Fatal("no history page")
	}
	if n := strings.Count(page, `<svg class="viz-chart" data-viz="dense" tabindex="0"`); n != 5 {
		t.Fatalf("%d charts, want 5", n)
	}
	h := g.history
	days := dateRange(h.Git[0].Date, h.AsOf)
	if n := strings.Count(page, "<tr><th scope=\"row\">"); n != 5*len(days) {
		t.Errorf("%d data rows, want %d", n, 5*len(days))
	}
	last := h.Git[len(h.Git)-1]
	reported, merged, p2 := 0, 0, 0
	for _, f := range g.findings {
		if f.Priority == "P2" {
			p2++
		}
	}
	if !strings.Contains(page, fmt.Sprintf(`data-last="P2 %d"`, p2)) {
		t.Error("P2 findings series does not end at the registry count")
	}
	for _, i := range h.Issues {
		if i.Reported {
			reported++
		}
	}
	for _, c := range h.Changes {
		if c.Own && c.Merged != "" {
			merged++
		}
	}
	for _, want := range []string{
		"Snapshot of " + h.AsOf,
		fmt.Sprintf(`data-last="Registered %d"`, last.Properties),
		fmt.Sprintf(`data-last="Theorem and lemma declarations %d"`, last.Theorems),
		fmt.Sprintf(`data-last="Reported %d"`, reported),
		fmt.Sprintf(`data-last="Merged %d"`, merged),
		fmt.Sprintf("The %d findings by priority", len(g.findings)),
	} {
		if !strings.Contains(page, want) {
			t.Errorf("history page lacks %q", want)
		}
	}
	if !regexp.MustCompile(`<g class="viz-pt" aria-label="\d{4}-\d{2}-\d{2}, `).MatchString(page) {
		t.Error("dense chart points do not start their aria-label with the date")
	}
	if strings.Contains(page, "\n\n<svg") || strings.Contains(strings.SplitN(page, "<figure", 2)[1], "\n\n</figure>") {
		t.Error("a blank line inside a figure ends the raw HTML block")
	}
}

func TestRejectHistorySnapshot(t *testing.T) {
	good := historySnapshot{AsOf: "2026-11-03", Git: []gitDay{{Date: "2026-11-01", Commit: "a", Commits: 1}, {Date: "2026-11-02", Commit: "b", Commits: 1}},
		Issues:  []issueEvent{{Ref: "golang/go#1", URL: "https://github.com/golang/go/issues/1", Opened: "2026-11-01", Closed: "2026-11-02"}},
		Changes: []changeEvent{{Number: 1, URL: "https://go-review.googlesource.com/c/go/+/1", Status: "MERGED", Mailed: "2026-11-01", Merged: "2026-11-02"}}}
	if err := validSnapshot(good); err != nil {
		t.Fatal(err)
	}
	for name, mutate := range map[string]func(*historySnapshot){
		"bad as_of":         func(s *historySnapshot) { s.AsOf = "soon" },
		"no git days":       func(s *historySnapshot) { s.Git = nil },
		"unordered git":     func(s *historySnapshot) { s.Git[0].Date, s.Git[1].Date = s.Git[1].Date, s.Git[0].Date },
		"as_of before git":  func(s *historySnapshot) { s.AsOf = "2026-11-01" },
		"closed before":     func(s *historySnapshot) { s.Issues[0].Closed = "2026-10-30" },
		"merged and status": func(s *historySnapshot) { s.Changes[0].Status = "NEW" },
		"bad change date":   func(s *historySnapshot) { s.Changes[0].Mailed = "x" },
		"after as_of":       func(s *historySnapshot) { s.Issues[0].Closed = "2026-11-04" },
	} {
		s := good
		s.Git = append([]gitDay(nil), good.Git...)
		s.Issues = append([]issueEvent(nil), good.Issues...)
		s.Changes = append([]changeEvent(nil), good.Changes...)
		mutate(&s)
		if err := validSnapshot(s); err == nil {
			t.Errorf("%s: accepted invalid snapshot", name)
		}
	}
	path := filepath.Join(t.TempDir(), "history.json")
	if err := os.WriteFile(path, []byte(`{"as_of":"2026-11-03","git":[],"issues":[],"changes":[],"extra":1}`), 0644); err != nil {
		t.Fatal(err)
	}
	if _, err := readSnapshot(path); err == nil {
		t.Error("accepted an unknown field")
	}
}

func TestLineChart(t *testing.T) {
	days := []string{"2026-11-01", "2026-11-02", "2026-11-03"}
	html := lineChart("x", "A <title>", "unit", days, []series{{Name: "One & two", Values: []int{0, 3, 7}}, {Name: "Other", Values: []int{1, 1, 2}}})
	for _, want := range []string{"A &lt;title&gt;", "One &amp; two", `data-last="One &amp; two 7"`, `<th scope="row">2026-11-03</th><td>7</td><td>2</td>`, "viz-legend", `aria-label="2026-11-03, One &amp; two: 7"`, `style="stroke:var(--viz-2)"`} {
		if !strings.Contains(html, want) {
			t.Errorf("chart lacks %q", want)
		}
	}
	if strings.Contains(html, "\n\n") {
		t.Error("blank line in chart HTML")
	}
	single := lineChart("y", "Only", "unit", days, []series{{Name: "Only", Values: []int{1, 2, 3}}})
	if strings.Contains(single, "viz-legend") {
		t.Error("a single series has a legend box")
	}
	for v, want := range map[int]int{0: 1, 1: 1, 3: 3, 7: 8, 10: 10, 17: 20, 76: 80, 2244: 3000} {
		if got := niceMax(v); got != want {
			t.Errorf("niceMax(%d) = %d, want %d", v, got, want)
		}
	}
	if got := dateRange("2026-10-31", "2026-11-02"); strings.Join(got, ",") != "2026-10-31,2026-11-01,2026-11-02" {
		t.Errorf("dateRange = %v", got)
	}
}

func TestSiteKitContract(t *testing.T) {
	root, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	g := &generator{root: root, pages: map[string][]byte{}, routes: map[string]string{}}
	if err := g.load(); err != nil {
		t.Fatal(err)
	}
	if err := g.render(); err != nil {
		t.Fatal(err)
	}
	home := string(g.pages["_index.md"])
	stamp := regexp.MustCompile(`<p class="data-stamp">Data at commit <a href="[^"]+"><code>[0-9a-f]{7,40}</code></a> \(\d{4}-\d{2}-\d{2}\)\.</p>`)
	if !stamp.MatchString(home) {
		t.Error("home page lacks the data stamp")
	}
	disclaimer := regexp.MustCompile(`(?s)<div class="disclaimer">(.*?)</div>`).FindStringSubmatch(home)
	if disclaimer == nil || !strings.Contains(disclaimer[1], "non-commercial") || !regexp.MustCompile(`\bAI\b`).MatchString(disclaimer[1]) {
		t.Error("disclaimer block lacks non-commercial or AI")
	}
	banner := regexp.MustCompile(`^<p class="site-banner"><img src="brand/([a-z-]+\.svg)" alt="[^"]+"`).FindStringSubmatch(strings.SplitN(home, "-->\n\n", 2)[1])
	if banner == nil {
		t.Error("the home page does not start with the site banner")
	} else if _, err := os.Stat(filepath.Join(root, "assets/brand", banner[1])); err != nil {
		t.Errorf("banner image: %v", err)
	}
	order := []string{"site-banner", "data-stamp", `class="disclaimer"`, "{{< stats >}}", "## Cite"}
	last := -1
	for _, s := range order {
		i := strings.Index(home, s)
		if i < last {
			t.Errorf("home page element %q out of order", s)
		}
		last = i
	}
	if n := strings.Count(home, "{{< stat "); n != 4 {
		t.Errorf("%d stat tiles, want 4", n)
	}
	for _, want := range []string{`relref "/findings"`, `relref "/methodology"`, `relref "/statuses"`, "0000-0001-9987-4338", "@software{"} {
		if !strings.Contains(home, want) {
			t.Errorf("home page lacks %q", want)
		}
	}
	statuses := string(g.pages["statuses/_index.md"])
	for _, w := range append(append([]string{}, statusWords()...), "kernel", "bv_decide", "open", "closed", "not planned", "new", "merged", "abandoned") {
		if !strings.Contains(statuses, quote(w)+" >}}") {
			t.Errorf("statuses page does not define %q", w)
		}
	}
	badgeRE := regexp.MustCompile(`\{\{< badge "[a-z]+" "([^"]+)" >\}\}`)
	for path, body := range g.pages {
		for _, m := range badgeRE.FindAllStringSubmatch(string(body), -1) {
			if !strings.Contains(statuses, quote(m[1])+" >}}") {
				t.Errorf("%s uses badge word %q that the statuses page does not define", path, m[1])
			}
		}
	}
	method := string(g.pages["methodology/_index.md"])
	if !strings.Contains(method, "site-kit v0.3.0") || !strings.Contains(method, "```mermaid") {
		t.Error("methodology page lacks the site-kit tag or the pipeline diagram")
	}
	for _, block := range regexp.MustCompile("(?s)```mermaid\n(.*?)```").FindAllStringSubmatch(method, -1) {
		for _, label := range regexp.MustCompile(`\[([^\]]*)\]|\(([^)]*)\)|\|([^|]*)\|`).FindAllString(block[1], -1) {
			if strings.ContainsAny(label, ";<#") {
				t.Errorf("Mermaid label %q contains ; < or #", label)
			}
		}
	}
	findex := string(g.pages["findings/_index.md"])
	if !strings.Contains(findex, `<div class="filterable">`) || strings.Count(findex, "\n|---") != 1 {
		t.Error("findings index is not one filterable table")
	}
	llms, full := string(g.pages["llms.txt"]), string(g.pages["llms-full.txt"])
	if !strings.Contains(llms, "non-commercial") || !strings.Contains(llms, "llms-full.txt") {
		t.Error("llms.txt lacks the disclaimer or the link to llms-full.txt")
	}
	for _, f := range g.findings {
		if !strings.Contains(full, f.ID) {
			t.Errorf("llms-full.txt lacks finding %s", f.ID)
		}
	}
	for _, p := range g.properties {
		if !strings.Contains(full, p.ID) {
			t.Errorf("llms-full.txt lacks property %s", p.ID)
		}
	}
	var registry struct {
		Findings   []map[string]any `json:"findings"`
		Properties []map[string]any `json:"properties"`
	}
	if err := json.Unmarshal(g.pages["registry.json"], &registry); err != nil || len(registry.Findings) != len(g.findings) || len(registry.Properties) != len(g.properties) {
		t.Errorf("registry.json: %v", err)
	}
	upstream := string(g.pages["upstream/_index.md"])
	for _, u := range g.upstreamTSV {
		if !strings.Contains(upstream, fmt.Sprintf("[%s %d](", u.Kind, u.Number)) {
			t.Errorf("upstream page lacks %s %s %d", u.Repo, u.Kind, u.Number)
		}
	}
	if !strings.Contains(upstream, "does not prove") {
		t.Error("upstream page lacks the release caveat")
	}
}

func TestRejectUpstreamTSV(t *testing.T) {
	head := "repo\tnumber\tkind\tstate\tcreated\tclosed\tmerged\tfixes\tcited_by\ttitle\n"
	good := head + "golang/go\t1\tissue\topen\t2026-11-01\t\t\t\tA\tt\n"
	if _, err := parseUpstreamTSV(good); err != nil {
		t.Fatal(err)
	}
	for name, bad := range map[string]string{
		"header":    "repo\tnumber\n",
		"kind":      head + "golang/go\t1\tbug\topen\t2026-11-01\t\t\t\t\tt\n",
		"state":     head + "golang/go\t1\tcl\topen\t2026-11-01\t\t\t\t\tt\n",
		"date":      head + "golang/go\t1\tissue\topen\tsoon\t\t\t\t\tt\n",
		"columns":   head + "golang/go\t1\tissue\topen\n",
		"number":    head + "golang/go\tx\tissue\topen\t2026-11-01\t\t\t\t\tt\n",
		"merged cl": head + "golang/go\t2\tcl\tmerged\t2026-11-01\t\t\t\t\tt\n",
		"bad fixes": head + "golang/go\t2\tcl\tnew\t2026-11-01\t\t\tnot-a-ref\t\tt\n",
		"duplicate": head + "golang/go\t1\tissue\topen\t2026-11-01\t\t\t\t\tt\n" + "golang/go\t1\tissue\topen\t2026-11-01\t\t\t\t\tt\n",
	} {
		if _, err := parseUpstreamTSV(bad); err == nil {
			t.Errorf("%s: accepted invalid TSV", name)
		}
	}
}

func TestCitation(t *testing.T) {
	cff := "cff-version: 1.2.0\nmessage: Cite it.\ntitle: \"go-in-lean: a title\"\nauthors:\n  - family-names: Celles\n    given-names: Sébastien\n    orcid: \"https://orcid.org/0000-0001-9987-4338\"\nrepository-code: \"https://github.com/s-celles/go-in-lean\"\nurl: \"https://s-celles.github.io/go-in-lean/\"\nlicense: MIT\n"
	c, err := parseCitation([]byte(cff))
	if err != nil {
		t.Fatal(err)
	}
	text := c.markdown("2026")
	for _, want := range []string{"Celles, S. (2026). *go-in-lean: a title*", "https://github.com/s-celles/go-in-lean", "author = {Celles, Sébastien}", "orcid.org/0000-0001-9987-4338"} {
		if !strings.Contains(text, want) {
			t.Errorf("citation lacks %q:\n%s", want, text)
		}
	}
	if _, err := parseCitation([]byte("cff-version: 1.2.0\n")); err == nil {
		t.Error("accepted a citation without title or authors")
	}
}

const disclosuresSample = "# comment\ncontributor\torcid\tproject\tkind\trole\tnote\n" +
	"Ann Example\t0000-0001-2345-6789\tGo (gc and the standard library)\texamined system\tcontributor\t3 issues\n" +
	"Ann Example\t0000-0001-2345-6789\tYaegi\tcompared system\tnone\t\n" +
	"Ann Example\t0000-0001-2345-6789\tnone\tother\tnone\tno funding\n" +
	"Ann Example\t0000-0001-2345-6789\tan AI assistant\tAI assistance\twrote drafts\treviewed by the contributor\n"

func TestDisclosures(t *testing.T) {
	rows, err := parseDisclosures(disclosuresSample)
	if err != nil {
		t.Fatal(err)
	}
	if len(rows) != 4 || rows[0].Contributor != "Ann Example" || rows[1].Kind != "compared system" {
		t.Fatalf("bad parse: %+v", rows)
	}
	page := disclosurePage(rows)
	for _, want := range []string{"| System or source | Ann Example |", "| Go (gc and the standard library) | contributor |", "| Yaegi | none |", "## Use of AI assistants", "wrote drafts", "0000-0001-2345-6789"} {
		if !strings.Contains(page, want) {
			t.Errorf("disclosure page lacks %q", want)
		}
	}
	if strings.Contains(page, "—") {
		t.Error("disclosure page contains an em dash")
	}
	head := "contributor\torcid\tproject\tkind\trole\tnote\n"
	for name, bad := range map[string]string{
		"kind":     head + "A\t0000-0001-2345-6789\tX\tfriend\tnone\t\n" + "A\t0000-0001-2345-6789\tan AI assistant\tAI assistance\tx\ty\n",
		"no AI":    head + "A\t0000-0001-2345-6789\tX\tcompared system\tnone\t\n",
		"orcid":    head + "A\t1234\tan AI assistant\tAI assistance\tx\ty\n",
		"columns":  head + "A\t0000-0001-2345-6789\tX\n",
		"header":   "who\twhat\n",
		"empty":    head,
		"nameless": head + "\t0000-0001-2345-6789\tan AI assistant\tAI assistance\tx\ty\n",
	} {
		if _, err := parseDisclosures(bad); err == nil {
			t.Errorf("%s: accepted invalid disclosures", name)
		}
	}
	root, err := filepath.Abs("../..")
	if err != nil {
		t.Fatal(err)
	}
	g := &generator{root: root, pages: map[string][]byte{}, routes: map[string]string{}}
	if err := g.load(); err != nil {
		t.Fatal(err)
	}
	if err := g.render(); err != nil {
		t.Fatal(err)
	}
	for _, path := range []string{"_index.md", "llms.txt"} {
		if !strings.Contains(string(g.pages[path]), disclosureSummary) {
			t.Errorf("%s lacks the disclosure summary", path)
		}
	}
	if !strings.Contains(string(g.pages["_index.md"]), `relref "/conflict-of-interest"`) || len(g.pages["conflict-of-interest/_index.md"]) == 0 {
		t.Error("no disclosure page or no link to it from the home page")
	}
}
