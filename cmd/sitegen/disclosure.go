package main

// Conflict of interest and AI assistance declarations (docs/disclosures.tsv),
// on the model shared by the project sites: one row per contributor and project.

import (
	"fmt"
	"regexp"
	"strings"
)

// disclosureSummary is the one-line summary on the home page, the footer, the
// README, CITATION.cff and llms.txt. It must agree with docs/disclosures.tsv.
const disclosureSummary = "Disclosure: the author reports issues and contributes fixes to Go, and has reported issues to Yaegi, as part of this project; has no funding, employment or other interest tied to the systems examined; and works with an AI assistant."

type disclosure struct {
	Contributor, ORCID, Project, Kind, Role, Note string
}

var disclosureColumns = []string{"contributor", "orcid", "project", "kind", "role", "note"}
var orcidRE = regexp.MustCompile(`^\d{4}-\d{4}-\d{4}-\d{3}[\dX]$`)

// validKind: the shared vocabulary, with "examined system" for the system under
// examination (Go) and "tool" for software used but not evaluated (Lean).
func validKind(k string) bool {
	switch k {
	case "examined system", "compared system", "tool", "benchmark", "AI assistance", "other":
		return true
	}
	return strings.HasPrefix(k, "source of ") && len(k) > len("source of ")
}

func parseDisclosures(text string) ([]disclosure, error) {
	var lines []string
	for _, l := range strings.Split(strings.TrimRight(text, "\n"), "\n") {
		if !strings.HasPrefix(l, "#") {
			lines = append(lines, l)
		}
	}
	if len(lines) == 0 || lines[0] != strings.Join(disclosureColumns, "\t") {
		return nil, fmt.Errorf("disclosures.tsv: missing or unexpected header")
	}
	var rows []disclosure
	ai := map[string]bool{}
	for i, l := range lines[1:] {
		f := strings.Split(l, "\t")
		if len(f) != len(disclosureColumns) {
			return nil, fmt.Errorf("disclosures.tsv row %d: %d columns", i+1, len(f))
		}
		d := disclosure{f[0], f[1], f[2], f[3], f[4], f[5]}
		if d.Contributor == "" || d.Project == "" || d.Role == "" {
			return nil, fmt.Errorf("disclosures.tsv row %d: contributor, project and role are required", i+1)
		}
		if d.ORCID != "" && !orcidRE.MatchString(d.ORCID) { // empty: no ORCID (site-kit 0.3.1)
			return nil, fmt.Errorf("disclosures.tsv row %d: invalid ORCID %q", i+1, d.ORCID)
		}
		if !validKind(d.Kind) {
			return nil, fmt.Errorf("disclosures.tsv row %d: unknown kind %q", i+1, d.Kind)
		}
		if strings.Contains(l, "—") {
			return nil, fmt.Errorf("disclosures.tsv row %d: em dash", i+1)
		}
		if d.Kind == "AI assistance" {
			ai[d.Contributor] = true
		}
		rows = append(rows, d)
	}
	if len(rows) == 0 {
		return nil, fmt.Errorf("disclosures.tsv: no declaration")
	}
	for _, d := range rows {
		if !ai[d.Contributor] {
			return nil, fmt.Errorf("disclosures.tsv: %s has no AI assistance row", d.Contributor)
		}
	}
	return rows, nil
}

func disclosurePage(rows []disclosure) string {
	var people []string
	orcid := map[string]string{}
	for _, d := range rows {
		if !contains(people, d.Contributor) {
			people = append(people, d.Contributor)
			orcid[d.Contributor] = d.ORCID
		}
	}
	s := disclosureSummary + "\n\nEvery contributor declares, in " + link("docs/disclosures.tsv", repoLink("docs/disclosures.tsv")) + ", their relation to each system the project examines or compares, to the tools it relies on, and their use of AI assistants. A row whose role is none is also a declaration.\n\n"
	for _, p := range people {
		s += "## " + p + "\n\n"
		if orcid[p] != "" {
			s += "ORCID " + link(orcid[p], "https://orcid.org/"+orcid[p]) + "\n\n"
		}
		s += "| Project | Kind | Role | Note |\n|---|---|---|---|\n"
		for _, d := range rows {
			if d.Contributor == p {
				s += "| " + cell(d.Project) + " | " + d.Kind + " | " + cell(d.Role) + " | " + cell(d.Note) + " |\n"
			}
		}
		s += "\n"
	}
	s += "## Systems and contributors\n\nOne row per system, source or tool, one column per contributor: the declared role, or none.\n\n| System or source |"
	for _, p := range people {
		s += " " + p + " |"
	}
	s += "\n|---|" + strings.Repeat("---|", len(people)) + "\n"
	var systems []string
	for _, d := range rows {
		if d.Kind != "AI assistance" && d.Kind != "other" && d.Kind != "benchmark" && !contains(systems, d.Project) {
			systems = append(systems, d.Project)
		}
	}
	for _, sys := range systems {
		s += "| " + cell(sys) + " |"
		for _, p := range people {
			role := "none"
			for _, d := range rows {
				if d.Contributor == p && d.Project == sys {
					role = d.Role
				}
			}
			s += " " + cell(role) + " |"
		}
		s += "\n"
	}
	s += "\n## Use of AI assistants\n\n| Contributor | What the assistant did | How the output was reviewed |\n|---|---|---|\n"
	for _, d := range rows {
		if d.Kind == "AI assistance" {
			s += "| " + cell(d.Contributor) + " | " + cell(d.Role) + " | " + cell(d.Note) + " |\n"
		}
	}
	s += "\n## What limits the bias\n\n- A model counterexample is never reported as a Go bug: it is reproduced first on a public Go toolchain, with the versions, architecture and flags recorded, and the reproducer is published with the finding.\n- The alternative implementations are compared on the same generated programs, judged by the same Lean oracle, with no program written for one implementation.\n- Upstream maintainers, not this project, decide what is a bug and whether a fix is merged; the Upstream page shows their decisions, including the issues closed without a fix and the CLs abandoned.\n- Code, data, reproducers and campaign commands are public, so every claim can be checked again.\n\n## Report a problem\n\nIf a finding, a comparison or a declaration here looks unfair or wrong, please open a " + link("GitHub issue", repository+"/issues") + ".\n"
	return s
}

func (g *generator) disclosureSection() error {
	b, err := g.read("docs/disclosures.tsv")
	if err != nil {
		return err
	}
	rows, err := parseDisclosures(string(b))
	if err != nil {
		return err
	}
	// site-kit SPEC 0.4: the page, the menu entry and docs/disclosures.tsv share one name;
	// the SPEC 0.3 address redirects here
	if err := g.page("disclosures/_index.md", "Disclosures", 42, nil, disclosurePage(rows)); err != nil {
		return err
	}
	meta := string(g.pages["disclosures/_index.md"])
	g.pages["disclosures/_index.md"] = []byte(strings.Replace(meta, "type: docs\n", "type: docs\naliases:\n    - /conflict-of-interest/\n", 1))
	return nil
}
