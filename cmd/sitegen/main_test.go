package main

import (
	"bytes"
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
