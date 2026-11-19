// sitegen builds Hugo content from the verification and finding manifests.
package main

import (
	"bytes"
	"encoding/json"
	"errors"
	"flag"
	"fmt"
	"io"
	"os"
	"path/filepath"
	"regexp"
	"sort"
	"strings"
	"time"

	"gopkg.in/yaml.v3"
)

const repository = "https://github.com/s-celles/go-in-lean"

var statuses = []string{"proved_in_model", "counterexample_in_model", "model_mismatch", "specification_ambiguity", "go_discrepancy_reproduced", "known_issue", "inconclusive"}
var labels = map[string]string{
	"proved_in_model": "Proved in model", "counterexample_in_model": "Model counterexample",
	"model_mismatch": "Model mismatch", "specification_ambiguity": "Specification ambiguity",
	"go_discrepancy_reproduced": "Reproduced in Go", "known_issue": "Known issue", "inconclusive": "Inconclusive",
}

type History struct {
	Date   string `yaml:"date"`
	Status string `yaml:"status"`
	Note   string `yaml:"note"`
}

type Property struct {
	ID            string    `yaml:"id"`
	Package       string    `yaml:"package"`
	Function      string    `yaml:"function"`
	GoSource      string    `yaml:"go_source"`
	Doc           string    `yaml:"doc"`
	Preconditions string    `yaml:"preconditions"`
	Postcondition string    `yaml:"postcondition"`
	LeanStatement string    `yaml:"lean_statement"`
	LeanTheorem   []string  `yaml:"lean_theorem"`
	Oracle        string    `yaml:"oracle"`
	AmbiguityRisk string    `yaml:"ambiguity_risk"`
	Complexity    string    `yaml:"complexity"`
	Trust         string    `yaml:"trust"`
	Status        string    `yaml:"status"`
	GoTests       []string  `yaml:"go_tests"`
	History       []History `yaml:"history"`
	Evidence      string    `yaml:"evidence"`
	Blocker       string    `yaml:"blocker"`
}

type Finding struct {
	ID               string    `yaml:"id"`
	Title            string    `yaml:"title"`
	Package          string    `yaml:"package"`
	Architectures    []string  `yaml:"architectures"`
	Priority         string    `yaml:"priority"`
	Severity         string    `yaml:"severity"`
	Status           string    `yaml:"status"`
	Summary          string    `yaml:"summary"`
	AffectedVersions string    `yaml:"affected_versions"`
	GoSource         string    `yaml:"go_source"`
	Report           string    `yaml:"report"`
	Reproducer       string    `yaml:"reproducer"`
	LeanFile         string    `yaml:"lean_file"`
	SourceRecords    []string  `yaml:"source_records"`
	Upstream         []string  `yaml:"upstream"`
	History          []History `yaml:"history"`
}

type source struct {
	Path string
	Line int
}
type upstreamRow struct{ Item, State, CL, CLState, Note string }
type generator struct {
	root       string
	properties []Property
	findings   []Finding
	theorems   map[string]source
	tests      map[string]source
	upstream   []upstreamRow
	history    *historySnapshot
	pages      map[string][]byte
	routes     map[string]string
}

func main() {
	root := flag.String("root", ".", "repository root")
	out := flag.String("out", "site/content", "generated content directory, relative to root")
	flag.Parse()
	if err := run(*root, *out); err != nil {
		fmt.Fprintln(os.Stderr, "sitegen:", err)
		os.Exit(1)
	}
}

func run(root, out string) error {
	abs, err := filepath.Abs(root)
	if err != nil {
		return err
	}
	g := &generator{root: abs, pages: map[string][]byte{}, routes: map[string]string{}}
	if err := g.load(); err != nil {
		return err
	}
	if err := g.render(); err != nil {
		return err
	}
	if !filepath.IsAbs(out) {
		out = filepath.Join(abs, out)
	}
	if err := writePages(out, g.pages); err != nil {
		return err
	}
	fmt.Printf("Generated %d properties, %d findings, %d upstream rows (%d Markdown pages).\n", len(g.properties), len(g.findings), len(g.upstream), len(g.pages))
	return nil
}

func decodeYAML(path string, dst any) error {
	b, err := os.ReadFile(path)
	if err != nil {
		return err
	}
	d := yaml.NewDecoder(bytes.NewReader(b))
	d.KnownFields(true)
	if err := d.Decode(dst); err != nil {
		return fmt.Errorf("%s: %w", path, err)
	}
	var extra any
	if err := d.Decode(&extra); err != io.EOF {
		return fmt.Errorf("%s: expected exactly one YAML document", path)
	}
	return nil
}

func validHistory(id, status string, history []History) error {
	if _, ok := labels[status]; !ok {
		return fmt.Errorf("%s: unknown status %q", id, status)
	}
	if len(history) == 0 {
		return fmt.Errorf("%s: history is required", id)
	}
	previous := ""
	for _, h := range history {
		if _, err := time.Parse("2006-01-02", h.Date); err != nil {
			return fmt.Errorf("%s: invalid history date %q", id, h.Date)
		}
		if h.Date < previous {
			return fmt.Errorf("%s: history is not chronological", id)
		}
		previous = h.Date
		if _, ok := labels[h.Status]; !ok {
			return fmt.Errorf("%s: unknown history status %q", id, h.Status)
		}
	}
	if history[len(history)-1].Status != status {
		return fmt.Errorf("%s: latest history status differs from status", id)
	}
	return nil
}

var idPattern = regexp.MustCompile(`^[A-Z0-9]+(?:-[A-Z0-9]+)*$`)

func (g *generator) load() error {
	var manifest struct {
		Properties []Property `yaml:"properties"`
	}
	if err := decodeYAML(filepath.Join(g.root, "targets/properties.yaml"), &manifest); err != nil {
		return err
	}
	if len(manifest.Properties) == 0 {
		return errors.New("empty property manifest")
	}
	g.properties = manifest.Properties
	sort.Slice(g.properties, func(i, j int) bool { return g.properties[i].ID < g.properties[j].ID })
	var err error
	g.theorems, g.tests, err = indexSources(g.root)
	if err != nil {
		return err
	}
	seen := map[string]bool{}
	for _, p := range g.properties {
		if !idPattern.MatchString(p.ID) || seen[p.ID] {
			return fmt.Errorf("invalid or duplicate property id %q", p.ID)
		}
		seen[p.ID] = true
		if p.Package == "" || p.Function == "" || p.Doc == "" || p.GoSource == "" || p.Postcondition == "" || p.LeanStatement == "" || p.Oracle == "" || p.Preconditions == "" || p.AmbiguityRisk == "" || p.Complexity == "" {
			return fmt.Errorf("%s: missing required property field", p.ID)
		}
		if p.Trust != "kernel" && p.Trust != "bv_decide" {
			return fmt.Errorf("%s: unknown trust tier %q", p.ID, p.Trust)
		}
		if err := validHistory(p.ID, p.Status, p.History); err != nil {
			return err
		}
		if p.Status == "proved_in_model" && len(p.LeanTheorem) == 0 {
			return fmt.Errorf("%s: proved property has no theorem", p.ID)
		}
		for _, name := range p.LeanTheorem {
			if _, ok := g.theorems[name]; !ok {
				return fmt.Errorf("%s: theorem source not found: %s", p.ID, name)
			}
		}
		for _, name := range p.GoTests {
			if _, ok := g.tests[name]; !ok {
				return fmt.Errorf("%s: Go test source not found: %s", p.ID, name)
			}
		}
	}
	files, err := filepath.Glob(filepath.Join(g.root, "findings/*.yaml"))
	if err != nil {
		return err
	}
	yml, err := filepath.Glob(filepath.Join(g.root, "findings/*.yml"))
	if err != nil {
		return err
	}
	files = append(files, yml...)
	sort.Strings(files)
	seen = map[string]bool{}
	for _, path := range files {
		var f Finding
		if err := decodeYAML(path, &f); err != nil {
			return err
		}
		if !idPattern.MatchString(f.ID) || seen[f.ID] {
			return fmt.Errorf("invalid or duplicate finding id %q", f.ID)
		}
		seen[f.ID] = true
		if strings.TrimSuffix(filepath.Base(path), filepath.Ext(path)) != f.ID {
			return fmt.Errorf("%s: filename must match finding id", path)
		}
		if f.Title == "" || f.Package == "" || f.Summary == "" || f.Severity == "" || f.AffectedVersions == "" || f.GoSource == "" || f.Report == "" || len(f.Architectures) == 0 {
			return fmt.Errorf("%s: missing required finding field", f.ID)
		}
		if f.Priority != "P0" && f.Priority != "P1" && f.Priority != "P2" && f.Priority != "P3" {
			return fmt.Errorf("%s: invalid priority", f.ID)
		}
		if err := validHistory(f.ID, f.Status, f.History); err != nil {
			return err
		}
		for _, p := range append([]string{f.Report, f.Reproducer, f.LeanFile}, f.SourceRecords...) {
			if p != "" {
				if _, err := g.read(p); err != nil {
					return fmt.Errorf("%s: %w", f.ID, err)
				}
			}
		}
		for _, u := range f.Upstream {
			if !strings.HasPrefix(u, "https://github.com/") {
				return fmt.Errorf("%s: invalid upstream URL", f.ID)
			}
		}
		g.findings = append(g.findings, f)
	}
	if len(g.findings) == 0 {
		return errors.New("no finding YAML manifests")
	}
	reports, _ := filepath.Glob(filepath.Join(g.root, "findings/*/finding.md"))
	for _, p := range reports {
		if !seen[filepath.Base(filepath.Dir(p))] {
			return fmt.Errorf("research record has no finding YAML: %s", p)
		}
	}
	sort.Slice(g.findings, func(i, j int) bool {
		a, b := g.findings[i], g.findings[j]
		if a.Priority != b.Priority {
			return a.Priority < b.Priority
		}
		return a.ID < b.ID
	})
	b, err := g.read("docs/upstream-status.md")
	if err != nil {
		return err
	}
	g.upstream, err = parseUpstream(string(b))
	if err != nil {
		return err
	}
	if g.history, err = readSnapshot(filepath.Join(g.root, "docs/history.json")); err != nil {
		return err
	}
	for _, f := range g.findings {
		for _, u := range f.Upstream {
			if len(g.upstreamFor(u)) == 0 {
				return fmt.Errorf("%s: upstream URL absent from docs/upstream-status.md: %s", f.ID, u)
			}
		}
	}
	return nil
}

func (g *generator) read(path string) ([]byte, error) {
	clean := filepath.ToSlash(filepath.Clean(path))
	if filepath.IsAbs(path) || clean == ".." || strings.HasPrefix(clean, "../") {
		return nil, fmt.Errorf("source path must stay in repository: %s", path)
	}
	return os.ReadFile(filepath.Join(g.root, path))
}

func writePages(out string, pages map[string][]byte) error {
	out = filepath.Clean(out)
	if out == string(filepath.Separator) || out == "." {
		return errors.New("refusing unsafe content destination")
	}
	if info, err := os.Stat(out); err == nil {
		if !info.IsDir() {
			return fmt.Errorf("output is not a directory: %s", out)
		}
		if _, err := os.Stat(filepath.Join(out, ".sitegen")); err != nil {
			return fmt.Errorf("refusing to replace content without .sitegen marker: %s", out)
		}
	} else if !errors.Is(err, os.ErrNotExist) {
		return err
	}
	parent := filepath.Dir(out)
	if err := os.MkdirAll(parent, 0755); err != nil {
		return err
	}
	tmp, err := os.MkdirTemp(parent, ".sitegen-")
	if err != nil {
		return err
	}
	defer os.RemoveAll(tmp)
	for _, name := range sortedKeys(pages) {
		p := filepath.Join(tmp, name)
		if err := os.MkdirAll(filepath.Dir(p), 0755); err != nil {
			return err
		}
		if err := os.WriteFile(p, pages[name], 0644); err != nil {
			return err
		}
	}
	if err := os.WriteFile(filepath.Join(tmp, ".sitegen"), []byte("Generated by cmd/sitegen. Do not edit.\n"), 0644); err != nil {
		return err
	}
	backup := out + ".previous"
	if _, err := os.Stat(backup); err == nil {
		return fmt.Errorf("backup path already exists: %s", backup)
	}
	exists := false
	if _, err := os.Stat(out); err == nil {
		exists = true
		if err := os.Rename(out, backup); err != nil {
			return err
		}
	}
	if err := os.Rename(tmp, out); err != nil {
		if exists {
			_ = os.Rename(backup, out)
		}
		return err
	}
	if exists {
		return os.RemoveAll(backup)
	}
	return nil
}

func sortedKeys[V any](m map[string]V) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}
func slug(s string) string {
	return strings.Trim(regexp.MustCompile(`[^a-z0-9]+`).ReplaceAllString(strings.ToLower(s), "-"), "-")
}
func quote(s string) string { b, _ := json.Marshal(s); return string(b) }
func cell(s string) string {
	return strings.ReplaceAll(strings.ReplaceAll(strings.ReplaceAll(s, `\|`, "|"), "|", `\|`), "\n", " ")
}
func link(label, url string) string {
	return "[" + strings.ReplaceAll(label, "]", `\]`) + "](" + strings.ReplaceAll(url, " ", "%20") + ")"
}
func repoLink(path string) string { return repository + "/blob/main/" + filepath.ToSlash(path) }
func sourceLink(s source) string  { return repoLink(s.Path) + fmt.Sprintf("#L%d", s.Line) }
func code(lang, s string) string {
	fence := "```"
	for strings.Contains(s, fence) {
		fence += "`"
	}
	return "\n" + fence + lang + "\n" + strings.TrimSpace(s) + "\n" + fence + "\n\n"
}
