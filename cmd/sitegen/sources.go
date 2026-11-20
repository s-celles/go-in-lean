package main

import (
	"fmt"
	"io/fs"
	"os"
	"path/filepath"
	"regexp"
	"strings"
)

// Keep line breaks while removing nested Lean comments, so source anchors stay exact.
func stripLeanComments(s string) string {
	b := []byte(s)
	depth := 0
	line := false
	quoted := false
	for i := 0; i < len(b); i++ {
		if b[i] == '\n' {
			line = false
			continue
		}
		if line {
			b[i] = ' '
			continue
		}
		if depth > 0 {
			if i+1 < len(b) && s[i:i+2] == "/-" {
				depth++
				b[i] = ' '
				i++
				b[i] = ' '
				continue
			}
			if i+1 < len(b) && s[i:i+2] == "-/" {
				depth--
				b[i] = ' '
				i++
				b[i] = ' '
				continue
			}
			b[i] = ' '
			continue
		}
		if quoted {
			if b[i] == '\\' {
				i++
				continue
			}
			if b[i] == '"' {
				quoted = false
			}
			continue
		}
		if b[i] == '"' {
			quoted = true
			continue
		}
		if i+1 < len(b) && s[i:i+2] == "--" {
			line = true
			b[i] = ' '
			i++
			b[i] = ' '
			continue
		}
		if i+1 < len(b) && s[i:i+2] == "/-" {
			depth = 1
			b[i] = ' '
			i++
			b[i] = ' '
		}
	}
	return string(b)
}

func indexSources(root string) (map[string]source, map[string]source, error) {
	theorems, tests := map[string]source{}, map[string]source{}
	scopeRE := regexp.MustCompile(`^\s*(namespace|section)\s*([^\s]*)`)
	endRE := regexp.MustCompile(`^\s*end(?:\s|$)`)
	declRE := regexp.MustCompile(`^\s*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev)\s+([A-Za-z0-9_.']+)`)
	testRE := regexp.MustCompile(`^func\s+((?:Test|Fuzz)[A-Za-z0-9_]+)\(`)
	for _, dir := range []string{"GoInLean", "go/tests", "go/reproducers"} {
		err := filepath.WalkDir(filepath.Join(root, dir), func(path string, d fs.DirEntry, err error) error {
			if err != nil {
				return err
			}
			if d.IsDir() {
				return nil
			}
			if !strings.HasSuffix(path, ".lean") && !strings.HasSuffix(path, ".go") {
				return nil
			}
			b, err := os.ReadFile(path)
			if err != nil {
				return err
			}
			rel, _ := filepath.Rel(root, path)
			rel = filepath.ToSlash(rel)
			if strings.HasSuffix(path, ".lean") {
				namespace := ""
				stack := []string{}
				for i, line := range strings.Split(stripLeanComments(string(b)), "\n") {
					if m := scopeRE.FindStringSubmatch(line); m != nil {
						stack = append(stack, namespace)
						if m[1] == "namespace" {
							if namespace != "" {
								namespace += "."
							}
							namespace += m[2]
						}
						continue
					}
					if endRE.MatchString(line) && len(stack) > 0 {
						namespace = stack[len(stack)-1]
						stack = stack[:len(stack)-1]
						continue
					}
					if m := declRE.FindStringSubmatch(line); m != nil {
						name := m[1]
						if strings.HasPrefix(name, "_root_.") {
							name = strings.TrimPrefix(name, "_root_.")
						} else if namespace != "" {
							name = namespace + "." + name
						}
						theorems[name] = source{rel, i + 1}
					}
				}
			} else {
				for i, line := range strings.Split(string(b), "\n") {
					if m := testRE.FindStringSubmatch(line); m != nil {
						if _, ok := tests[m[1]]; !ok {
							tests[m[1]] = source{rel, i + 1}
						}
					}
				}
			}
			return nil
		})
		if err != nil {
			return nil, nil, err
		}
	}
	return theorems, tests, nil
}

// A pipe inside a code span or escaped with a backslash is not a table separator.
func tableCells(line string) []string {
	line = strings.TrimSpace(line)
	if !strings.HasPrefix(line, "|") {
		return nil
	}
	line = strings.TrimSuffix(strings.TrimPrefix(line, "|"), "|")
	var cells []string
	start := 0
	tickRun := 0
	for i := 0; i < len(line); i++ {
		if line[i] == '\\' {
			i++
			continue
		}
		if line[i] == '`' {
			j := i
			for j < len(line) && line[j] == '`' {
				j++
			}
			n := j - i
			if tickRun == 0 {
				tickRun = n
			} else if tickRun == n {
				tickRun = 0
			}
			i = j - 1
			continue
		}
		if line[i] == '|' && tickRun == 0 {
			cells = append(cells, strings.TrimSpace(line[start:i]))
			start = i + 1
		}
	}
	return append(cells, strings.TrimSpace(line[start:]))
}

func parseUpstream(text string) ([]upstreamRow, error) {
	var rows []upstreamRow
	for _, line := range strings.Split(text, "\n") {
		c := tableCells(line)
		if len(c) < 3 {
			continue
		}
		if !strings.Contains(line, "https://github.com/") && !strings.Contains(line, "https://go-review.googlesource.com/") {
			continue
		}
		var r upstreamRow
		switch len(c) {
		case 5:
			r = upstreamRow{c[0], c[1], c[2], c[3], c[4]}
		case 4:
			if strings.Contains(c[0], "](") {
				r = upstreamRow{c[0], c[1], c[2], "See record", c[3]}
			} else {
				r = upstreamRow{c[1], c[2], "none", "none", c[3]}
			}
		case 3:
			r = upstreamRow{c[0], c[1], "none", "none", c[2]}
		default:
			return nil, fmt.Errorf("malformed upstream table row (%d columns): %s", len(c), line)
		}
		rows = append(rows, r)
	}
	if len(rows) == 0 {
		return nil, fmt.Errorf("no upstream status rows found")
	}
	return rows, nil
}

var urlRE = regexp.MustCompile(`https://[^\s)]+`)

func (g *generator) upstreamFor(url string) []upstreamRow {
	var out []upstreamRow
	for _, r := range g.upstream {
		for _, u := range urlRE.FindAllString(r.Item, -1) {
			if strings.Split(u, "#")[0] == url {
				out = append(out, r)
				break
			}
		}
	}
	return out
}

// Rewrite repository-relative links when importing research docs. Known site
// pages get local relrefs; other evidence links keep their exact GitHub path.
var markdownLinkRE = regexp.MustCompile(`(!?\[[^\]\n]*\])\(([^\s)]+)([^)]*)\)`)
var localPages = map[string]string{
	"README.md": "/docs/project", "docs/project.md": "/docs/project", "docs/upstream-status.md": "/upstream", "upstream-bugs.md": "/docs/upstream-bugs",
	"docs/prior-art.md": "/docs/prior-art", "docs/fuzzing-vision.md": "/docs/fuzzing-vision", "docs/cedar-notes.md": "/docs/cedar-notes", "CHANGELOG.md": "/docs/changelog", "docs/site.md": "/docs/site",
}

func rewriteLinks(text, path string) string {
	return markdownLinkRE.ReplaceAllStringFunc(text, func(s string) string {
		m := markdownLinkRE.FindStringSubmatch(s)
		dest := m[2]
		if strings.HasPrefix(dest, "#") || strings.Contains(dest, ":") || strings.HasPrefix(dest, "//") {
			return s
		}
		parts := strings.SplitN(dest, "#", 2)
		rel := filepath.ToSlash(filepath.Clean(filepath.Join(filepath.Dir(path), parts[0])))
		fragment := ""
		if len(parts) == 2 {
			fragment = "#" + parts[1]
		}
		if page, ok := localPages[rel]; ok && !strings.HasPrefix(m[1], "!") {
			return m[1] + "({{< relref " + quote(page) + " >}}" + fragment + m[3] + ")"
		}
		return m[1] + "(" + repoLink(rel) + fragment + m[3] + ")"
	})
}

var goPathRE = regexp.MustCompile(`(?:src/[A-Za-z0-9_./-]+\.[A-Za-z]+|(?:(?:_gen|ssa|ssagen|ssacompile)/)?(?:[A-Za-z0-9_]+\.rules|intrinsics\.go|prove\.go|known_bits\.go|regalloc\.go))(?::[0-9]+(?:-[0-9]+)?)?`)
var masterRevisionRE = regexp.MustCompile(`(?:master|Go master) ([a-f0-9]{8,40})`)

func goSourceLinks(text string) string {
	revision := "go1.25.5"
	if m := masterRevisionRE.FindStringSubmatch(text); m != nil {
		revision = m[1]
	}
	matched := false
	out := goPathRE.ReplaceAllStringFunc(text, func(citation string) string {
		matched = true
		parts := strings.SplitN(citation, ":", 2)
		path := parts[0]
		if !strings.HasPrefix(path, "src/") {
			switch {
			case strings.HasPrefix(path, "_gen/"):
				path = "src/cmd/compile/internal/ssa/" + path
			case strings.HasPrefix(path, "ssa/"):
				path = "src/cmd/compile/internal/" + path
			case strings.HasPrefix(path, "ssagen/"), strings.HasPrefix(path, "ssacompile/"):
				path = "src/cmd/compile/internal/" + path
			case strings.HasSuffix(path, ".rules"):
				path = "src/cmd/compile/internal/ssa/_gen/" + path
			case path == "intrinsics.go":
				path = "src/cmd/compile/internal/ssagen/" + path
			default:
				path = "src/cmd/compile/internal/ssa/" + path
			}
		}
		u := "https://github.com/golang/go/blob/" + revision + "/" + path
		if len(parts) == 2 {
			u += "#L" + strings.ReplaceAll(parts[1], "-", "-L")
		}
		return link(citation, u)
	})
	if !matched {
		return link(text, repoLink("targets/properties.yaml"))
	}
	return out
}
