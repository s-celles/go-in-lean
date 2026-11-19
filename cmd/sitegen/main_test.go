package main

import (
	"bytes"
	"fmt"
	"os"
	"path/filepath"
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
	if !bytes.Contains(g.pages["_index.md"], []byte("registered=\""+strconv.Itoa(len(g.properties))+"\"")) {
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
	if n := strings.Count(page, `<figure class="hchart"`); n != 5 {
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
		if c.Merged != "" {
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
	for _, want := range []string{"A &lt;title&gt;", "One &amp; two", `data-last="One &amp; two 7"`, `<th scope="row">2026-11-03</th><td>7</td><td>2</td>`, "hchart-legend"} {
		if !strings.Contains(html, want) {
			t.Errorf("chart lacks %q", want)
		}
	}
	if strings.Contains(html, "\n\n") {
		t.Error("blank line in chart HTML")
	}
	single := lineChart("y", "Only", "unit", days, []series{{Name: "Only", Values: []int{1, 2, 3}}})
	if strings.Contains(single, "hchart-legend") {
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
