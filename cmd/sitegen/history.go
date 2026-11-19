package main

import (
	"bytes"
	"encoding/json"
	"fmt"
	"html"
	"math"
	"os"
	"sort"
	"strings"
	"time"
)

// docs/history.json, written by scripts/history.py: a checked-in snapshot of the
// repository's git history and of the project's upstream issues and CLs.
type historySnapshot struct {
	AsOf    string        `json:"as_of"`
	Git     []gitDay      `json:"git"`
	Issues  []issueEvent  `json:"issues"`
	Changes []changeEvent `json:"changes"`
}
type gitDay struct {
	Date       string `json:"date"`
	Commit     string `json:"commit"`
	Commits    int    `json:"commits"`
	Theorems   int    `json:"theorems"`
	Properties int    `json:"properties"`
	Proved     int    `json:"proved"`
}
type issueEvent struct {
	Ref      string `json:"ref"`
	URL      string `json:"url"`
	Reported bool   `json:"reported"`
	Opened   string `json:"opened"`
	Closed   string `json:"closed"`
}
type changeEvent struct {
	Number    int    `json:"number"`
	URL       string `json:"url"`
	Status    string `json:"status"`
	Mailed    string `json:"mailed"`
	Merged    string `json:"merged"`
	Abandoned string `json:"abandoned"`
}

func readSnapshot(path string) (*historySnapshot, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	d := json.NewDecoder(bytes.NewReader(b))
	d.DisallowUnknownFields()
	var s historySnapshot
	if err := d.Decode(&s); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	if err := validSnapshot(s); err != nil {
		return nil, fmt.Errorf("%s: %w", path, err)
	}
	return &s, nil
}

func validDate(d string) bool {
	_, err := time.Parse("2006-01-02", d)
	return err == nil
}

func validSnapshot(s historySnapshot) error {
	if !validDate(s.AsOf) {
		return fmt.Errorf("invalid as_of %q", s.AsOf)
	}
	if len(s.Git) == 0 {
		return fmt.Errorf("no git days")
	}
	for i, d := range s.Git {
		if !validDate(d.Date) || (i > 0 && d.Date <= s.Git[i-1].Date) || d.Commits <= 0 || d.Commit == "" {
			return fmt.Errorf("git day %d (%q) is invalid or out of order", i, d.Date)
		}
		if d.Theorems < 0 || d.Properties < 0 || d.Proved < 0 || d.Proved > d.Properties {
			return fmt.Errorf("git day %s has inconsistent counts", d.Date)
		}
	}
	if s.AsOf < s.Git[len(s.Git)-1].Date {
		return fmt.Errorf("as_of %s precedes the last git day", s.AsOf)
	}
	// an event date may be empty (not happened); when present it is a day no later than as_of
	event := func(what, d string) error {
		if d != "" && (!validDate(d) || d > s.AsOf) {
			return fmt.Errorf("%s: invalid date %q", what, d)
		}
		return nil
	}
	for _, i := range s.Issues {
		if !strings.HasPrefix(i.URL, "https://github.com/") || i.Opened == "" {
			return fmt.Errorf("issue %q: missing URL or opening date", i.Ref)
		}
		if err := event(i.Ref, i.Opened); err != nil {
			return err
		}
		if err := event(i.Ref, i.Closed); err != nil {
			return err
		}
		if i.Closed != "" && i.Closed < i.Opened {
			return fmt.Errorf("issue %s closed before it was opened", i.Ref)
		}
	}
	for _, c := range s.Changes {
		what := fmt.Sprintf("CL %d", c.Number)
		if !strings.HasPrefix(c.URL, "https://go-review.googlesource.com/") || c.Mailed == "" {
			return fmt.Errorf("%s: missing URL or mailing date", what)
		}
		for _, d := range []string{c.Mailed, c.Merged, c.Abandoned} {
			if err := event(what, d); err != nil {
				return err
			}
			if d != "" && d < c.Mailed {
				return fmt.Errorf("%s: event before mailing", what)
			}
		}
		if (c.Merged != "") != (c.Status == "MERGED") || (c.Abandoned != "") != (c.Status == "ABANDONED") {
			return fmt.Errorf("%s: dates disagree with status %s", what, c.Status)
		}
	}
	return nil
}

// dateRange lists every calendar day from first to last, inclusive.
func dateRange(first, last string) []string {
	a, _ := time.Parse("2006-01-02", first)
	b, _ := time.Parse("2006-01-02", last)
	var days []string
	for d := a; !d.After(b); d = d.AddDate(0, 0, 1) {
		days = append(days, d.Format("2006-01-02"))
	}
	return days
}

// cumulative counts, for each day, the dates that are on or before it.
func cumulative(days []string, dates []string) []int {
	sort.Strings(dates)
	out := make([]int, len(days))
	j := 0
	for i, d := range days {
		for j < len(dates) && dates[j] <= d {
			j++
		}
		out[i] = j
	}
	return out
}

type series struct {
	Name   string
	Values []int
}

// tickStep is the smallest 1, 2, 2.5 or 5 times a power of ten that splits v into at most four steps.
func tickStep(v int) int {
	if v <= 4 {
		return 1
	}
	raw := float64(v) / 4
	p := math.Pow(10, math.Floor(math.Log10(raw)))
	for _, m := range []float64{1, 2, 2.5, 5, 10} {
		if s := m * p; s >= raw && s == math.Trunc(s) {
			return int(s)
		}
	}
	return int(10 * p)
}

// niceMax is the axis maximum: v rounded up to a whole number of tick steps.
func niceMax(v int) int {
	if v <= 0 {
		return 1
	}
	s := tickStep(v)
	return (v + s - 1) / s * s
}

func shortDate(d string) string {
	t, _ := time.Parse("2006-01-02", d)
	return t.Format("Jan 2")
}

func thousands(n int) string {
	s := fmt.Sprint(n)
	for i := len(s) - 3; i > 0; i -= 3 {
		s = s[:i] + "," + s[i:]
	}
	return s
}

// lineChart renders one figure: an inline SVG line chart on one y-axis, an HTML
// legend for two or more series, and a data table. The HTML has no blank line, so
// Goldmark keeps it as one raw block. history.js adds the crosshair and tooltip.
func lineChart(id, title, unit string, days []string, ss []series) string {
	const w, hgt, left, right, top, bottom = 720.0, 240.0, 52.0, 150.0, 12.0, 28.0
	pw, ph := w-left-right, hgt-top-bottom
	maxV := 0
	for _, s := range ss {
		for _, v := range s.Values {
			if v > maxV {
				maxV = v
			}
		}
	}
	ymax := niceMax(maxV)
	x := func(i int) float64 {
		if len(days) == 1 {
			return left + pw/2
		}
		return left + pw*float64(i)/float64(len(days)-1)
	}
	y := func(v int) float64 { return top + ph*(1-float64(v)/float64(ymax)) }
	esc := html.EscapeString
	var b strings.Builder
	data, _ := json.Marshal(map[string]any{"dates": days, "series": ss})
	fmt.Fprintf(&b, `<figure class="hchart" id="%s" data-chart="%s">`, esc(id), esc(string(data)))
	fmt.Fprintf(&b, `<figcaption><strong>%s</strong> <span>%s</span></figcaption>`, esc(title), esc(unit))
	if len(ss) > 1 {
		b.WriteString(`<ul class="hchart-legend">`)
		for i, s := range ss {
			fmt.Fprintf(&b, `<li><span class="hchart-key hchart-s%d"></span>%s</li>`, i+1, esc(s.Name))
		}
		b.WriteString(`</ul>`)
	}
	b.WriteString(`<div class="hchart-plot">`)
	fmt.Fprintf(&b, `<svg viewBox="0 0 %.0f %.0f" role="img" aria-label="%s, %s to %s" focusable="false">`, w, hgt, esc(title), days[0], days[len(days)-1])
	for v := 0; v <= ymax; v += tickStep(maxV) {
		fmt.Fprintf(&b, `<line class="hchart-grid" x1="%.1f" x2="%.1f" y1="%.1f" y2="%.1f"/>`, left, left+pw, y(v), y(v))
		fmt.Fprintf(&b, `<text class="hchart-tick" x="%.1f" y="%.1f" text-anchor="end" dominant-baseline="middle">%s</text>`, left-8, y(v), thousands(v))
	}
	step := 7
	for i := 0; i < len(days); i += step {
		fmt.Fprintf(&b, `<text class="hchart-tick" x="%.1f" y="%.1f" text-anchor="middle">%s</text>`, x(i), hgt-8, shortDate(days[i]))
	}
	labelY := []float64{}
	for si, s := range ss {
		var pts []string
		for i, v := range s.Values {
			pts = append(pts, fmt.Sprintf("%.1f,%.1f", x(i), y(v)))
		}
		last := s.Values[len(s.Values)-1]
		fmt.Fprintf(&b, `<polyline class="hchart-line hchart-s%d" points="%s"/>`, si+1, strings.Join(pts, " "))
		fmt.Fprintf(&b, `<circle class="hchart-dot hchart-s%d" cx="%.1f" cy="%.1f" r="4"/>`, si+1, x(len(days)-1), y(last))
		// direct end label, skipped when it would collide with an earlier one (the legend still names it)
		ly, clash := y(last), false
		for _, o := range labelY {
			if math.Abs(o-ly) < 14 {
				clash = true
			}
		}
		if !clash {
			labelY = append(labelY, ly)
			label := thousands(last) // a single series is named by the title
			if len(ss) > 1 {
				label = esc(s.Name) + " " + label
			}
			fmt.Fprintf(&b, `<text class="hchart-end" x="%.1f" y="%.1f" dominant-baseline="middle">%s</text>`, x(len(days)-1)+10, ly, label)
		}
	}
	fmt.Fprintf(&b, `<line class="hchart-cross" x1="0" x2="0" y1="%.1f" y2="%.1f" visibility="hidden"/>`, top, top+ph)
	b.WriteString(`</svg></div><div class="hchart-tip" hidden></div>`)
	for _, s := range ss {
		fmt.Fprintf(&b, `<span hidden data-last="%s %d"></span>`, esc(s.Name), s.Values[len(s.Values)-1])
	}
	b.WriteString(`<details class="hchart-data"><summary>Data table</summary><table><thead><tr><th scope="col">Date</th>`)
	for _, s := range ss {
		fmt.Fprintf(&b, `<th scope="col">%s</th>`, esc(s.Name))
	}
	b.WriteString(`</tr></thead><tbody>`)
	for i, d := range days {
		fmt.Fprintf(&b, `<tr><th scope="row">%s</th>`, d)
		for _, s := range ss {
			fmt.Fprintf(&b, `<td>%d</td>`, s.Values[i])
		}
		b.WriteString(`</tr>`)
	}
	b.WriteString(`</tbody></table></details></figure>`)
	return b.String()
}

func (g *generator) historyPage() error {
	h := g.history
	days := dateRange(h.Git[0].Date, h.AsOf)
	// git values carry forward over days without commits
	carry := func(f func(gitDay) int) []int {
		out := make([]int, len(days))
		j, v := 0, 0
		for i, d := range days {
			for j < len(h.Git) && h.Git[j].Date <= d {
				v = f(h.Git[j])
				j++
			}
			out[i] = v
		}
		return out
	}
	byPriority := map[string][]string{}
	for _, f := range g.findings {
		byPriority[f.Priority] = append(byPriority[f.Priority], f.History[0].Date)
	}
	var findings []series
	for _, p := range []string{"P0", "P1", "P2", "P3"} {
		if len(byPriority[p]) > 0 {
			findings = append(findings, series{Name: p, Values: cumulative(days, byPriority[p])})
		}
	}
	var opened, closed, mailed, merged, abandoned []string
	reported := 0
	for _, i := range h.Issues {
		if !i.Reported {
			continue
		}
		reported++
		opened = append(opened, i.Opened)
		if i.Closed != "" {
			closed = append(closed, i.Closed)
		}
	}
	for _, c := range h.Changes {
		mailed = append(mailed, c.Mailed)
		if c.Merged != "" {
			merged = append(merged, c.Merged)
		}
		if c.Abandoned != "" {
			abandoned = append(abandoned, c.Abandoned)
		}
	}
	body := "Snapshot of " + h.AsOf + ", from " + link("docs/history.json", repoLink("docs/history.json")) + ", written by " + link("scripts/history.py", repoLink("scripts/history.py")) + ". Like the upstream status page, it is a checked-in snapshot: the site does not query GitHub or Gerrit in your browser. Counts are cumulative and use calendar days: committer dates for the repository, UTC for GitHub and Gerrit. Days without commits keep the previous value.\n\n"
	body += "## Formal development\n\nCounted at each day's last commit. Declarations are `theorem` and `lemma` lines under `GoInLean/`, outside comments; generated rule files are included. Registry entries come from `targets/properties.yaml`, so entries, theorems and findings are different units.\n\n"
	body += lineChart("theorems", "Lean theorem and lemma declarations", "declarations", days, []series{{Name: "Theorem and lemma declarations", Values: carry(func(d gitDay) int { return d.Theorems })}}) + "\n\n"
	body += lineChart("properties", "Property registry", "entries", days, []series{
		{Name: "Registered", Values: carry(func(d gitDay) int { return d.Properties })},
		{Name: "Proved in model", Values: carry(func(d gitDay) int { return d.Proved })}}) + "\n\n"
	body += fmt.Sprintf("## Findings\n\nThe %d findings by priority, each counted from the first date in its history. A finding is not automatically a Go bug; see the "+ref("findings registry", "/findings")+".\n\n", len(g.findings))
	body += lineChart("findings", "Research findings by priority", "findings", days, findings) + "\n\n"
	body += fmt.Sprintf("## Upstream reports\n\nThe %d GitHub issues opened by the project among those tracked in the "+ref("upstream status", "/upstream")+", and its %d Go Gerrit CLs. A closed issue or a merged master CL does not establish that release branches contain the fix.\n\n", reported, len(h.Changes))
	body += lineChart("issues", "Issues reported upstream", "issues", days, []series{
		{Name: "Reported", Values: cumulative(days, opened)}, {Name: "Closed", Values: cumulative(days, closed)}}) + "\n\n"
	body += lineChart("changes", "Gerrit CLs", "CLs", days, []series{
		{Name: "Mailed", Values: cumulative(days, mailed)}, {Name: "Merged", Values: cumulative(days, merged)},
		{Name: "Abandoned", Values: cumulative(days, abandoned)}}) + "\n"
	return g.page("history/_index.md", "History", 25, nil, body)
}
