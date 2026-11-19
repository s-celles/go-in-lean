#!/usr/bin/env python3
"""Write docs/history.json, the dated snapshot behind the website's History page.

The snapshot has three parts:

* git: for each day with commits, the day's last commit, its number of Lean
  theorem/lemma declarations under GoInLean/, and the registered and
  proved_in_model entries of targets/properties.yaml at that commit;
* issues: every GitHub issue linked from docs/upstream-status.md, with the
  dates it was opened and closed and whether the project reported it;
* changes: every Go Gerrit CL owned by the project account or listed in
  docs/upstream-status.md, with the dates it was mailed, merged or abandoned
  and whether the project owns it.

It also writes docs/upstream.tsv, the upstream snapshot of the site-kit SPEC
(§6): one row per issue and CL with repo, number, kind, state, created, closed,
merged, fixes (the issue a CL fixes, from its row in docs/upstream-status.md),
cited_by (the findings whose manifest links the issue) and title.

Like docs/upstream-status.md, it is a checked-in snapshot: the site build reads
it and never queries GitHub or Gerrit. Re-run it to refresh the snapshot:

  python3 -I scripts/history.py            # writes docs/history.json
  python3 -I scripts/history.py --offline  # git part only, keeps the stored upstream part

Dates are calendar days: committer dates as recorded by git, UTC for GitHub and
Gerrit. GITHUB_TOKEN, if set, raises the GitHub API rate limit.
"""

import argparse
import datetime
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time
import urllib.error
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
OUTPUT = ROOT / "docs" / "history.json"
TSV = ROOT / "docs" / "upstream.tsv"
TSV_COLUMNS = ("repo", "number", "kind", "state", "created", "closed", "merged", "fixes", "cited_by", "title")
REPORTERS = {"s-celles", "s-celles-bot"}  # GitHub accounts the project reports from
GERRIT = "https://go-review.googlesource.com"
GERRIT_OWNER = 5287605  # public Gerrit account id of the project's CL author

ISSUE_RE = re.compile(r"https://github\.com/([\w.-]+/[\w.-]+)/issues/(\d+)")
CL_RE = re.compile(r"https://go-review\.googlesource\.com/c/go/\+/(\d+)")
DECL_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s",
                     re.M)


def issue_urls(status_text):
    """(repo, number) of each GitHub issue linked from the status table, first-seen order."""
    seen = []
    for repo, number in ISSUE_RE.findall(status_text):
        key = (repo, int(number))
        if key not in seen:
            seen.append(key)
    return seen


def cl_fixes(status_text):
    """{CL number: issue ref} for each CL listed on the same table row as one issue."""
    fixes = {}
    for line in status_text.splitlines():
        issues = issue_urls(line)
        if len(issues) == 1:
            for n in CL_RE.findall(line):
                fixes.setdefault(int(n), f"{issues[0][0]}#{issues[0][1]}")
    return fixes


def cited_by(manifests):
    """{issue ref: sorted finding ids} from {finding id: manifest text}."""
    out = {}
    for fid, text in sorted(manifests.items()):
        for repo, number in sorted(set(ISSUE_RE.findall(text))):
            out.setdefault(f"{repo}#{number}", []).append(fid)
    return out


def issue_state(api):
    if api["state"] == "open":
        return "open"
    return "not planned" if api.get("state_reason") == "not_planned" else "closed"


def clean(text):
    return " ".join((text or "").split())


def upstream_tsv(issues, changes, fixes, cites):
    rows = ["\t".join(TSV_COLUMNS)]
    for i in issues:
        repo, number = i["ref"].split("#")
        rows.append("\t".join([repo, number, "issue", i["state"], i["opened"], i["closed"] or "", "", "",
                               " ".join(cites.get(i["ref"], [])), clean(i["title"])]))
    for c in changes:
        fix = fixes.get(c["number"], "")
        closed = c["abandoned"] or ""
        rows.append("\t".join(["golang/go", str(c["number"]), "cl", c["status"].lower(), c["mailed"], closed,
                               c["merged"] or "", fix, " ".join(cites.get(fix, [])), clean(c["subject"])]))
    return "\n".join(rows) + "\n"


def property_counts(yaml_text):
    """(registered, proved_in_model) entries of a targets/properties.yaml text."""
    registered = len(re.findall(r"^  - id:", yaml_text, re.M))
    proved = len(re.findall(r'^    status:\s*"?proved_in_model"?\s*$', yaml_text, re.M))
    return registered, proved


def strip_lean_comments(text):
    """Remove (nested) block comments and line comments."""
    out, depth, i = [], 0, 0
    while i < len(text):
        if text.startswith("/-", i):
            depth += 1
            i += 2
        elif depth and text.startswith("-/", i):
            depth -= 1
            i += 2
        elif depth:
            if text[i] == "\n":
                out.append("\n")
            i += 1
        else:
            out.append(text[i])
            i += 1
    return re.sub(r"--.*", "", "".join(out))


def declarations(lean_text):
    """Number of theorem/lemma declarations outside comments."""
    return len(DECL_RE.findall(strip_lean_comments(lean_text)))


def day(timestamp):
    return timestamp[:10] if timestamp else None


def issue_record(key, api):
    repo, number = key
    return {"ref": f"{repo}#{number}", "url": f"https://github.com/{repo}/issues/{number}",
            "reported": api["user"]["login"] in REPORTERS,
            "opened": day(api["created_at"]), "closed": day(api.get("closed_at")),
            "state": issue_state(api), "title": clean(api["title"])}


def change_record(change):
    abandoned = None
    if change["status"] == "ABANDONED":
        for m in change.get("messages", []):
            if m["message"].startswith("Abandoned"):
                abandoned = day(m["date"])
    return {"number": change["_number"], "url": f"{GERRIT}/c/go/+/{change['_number']}",
            "status": change["status"], "mailed": day(change["created"]),
            "merged": day(change.get("submitted")), "abandoned": abandoned,
            "subject": clean(change["subject"]),
            "own": change.get("owner", {}).get("_account_id") == GERRIT_OWNER}


def daily_commits(log):
    """[(date, last commit of the day, commits that day)] from 'hash date' lines, oldest first."""
    days = {}
    for line in log.splitlines():
        rev, date = line.split()
        last, n = days.get(date, (None, 0))
        days[date] = (rev, n + 1)
    return [(d, rev, n) for d, (rev, n) in sorted(days.items())]


def git(*args):
    return subprocess.run(["git", *args], cwd=ROOT, capture_output=True, text=True, check=True).stdout


def git_series():
    series = []
    for date, rev, n in daily_commits(git("log", "--reverse", "--format=%H %cs", "HEAD")):
        files = [f for f in git("ls-tree", "-r", "--name-only", rev).splitlines()
                 if f.endswith(".lean") and (f.startswith("GoInLean/") or f == "GoInLean.lean")]
        theorems = sum(declarations(git("show", f"{rev}:{f}")) for f in files)
        try:
            registered, proved = property_counts(git("show", f"{rev}:targets/properties.yaml"))
        except subprocess.CalledProcessError:
            registered, proved = 0, 0
        series.append({"date": date, "commit": rev[:10], "commits": n, "theorems": theorems,
                       "properties": registered, "proved": proved})
    return series


def fetch_json(url, headers=None, gerrit=False):
    req = urllib.request.Request(url, headers={"User-Agent": "go-in-lean-history", **(headers or {})})
    for attempt in range(3):  # transient resets happen; a fourth failure is reported
        try:
            with urllib.request.urlopen(req, timeout=30) as r:
                body = r.read().decode()
            break
        except (urllib.error.URLError, ConnectionError, TimeoutError):
            if attempt == 2:
                raise
            time.sleep(2 * (attempt + 1))
    return json.loads(body[4:] if gerrit else body)  # Gerrit prefixes its JSON with )]}'


def upstream():
    headers = {"Accept": "application/vnd.github+json"}
    if os.environ.get("GITHUB_TOKEN"):
        headers["Authorization"] = "Bearer " + os.environ["GITHUB_TOKEN"]
    status = (ROOT / "docs" / "upstream-status.md").read_text()
    issues = [issue_record(k, fetch_json(f"https://api.github.com/repos/{k[0]}/issues/{k[1]}", headers))
              for k in issue_urls(status)]
    found = fetch_json(f"{GERRIT}/changes/?q=owner:{GERRIT_OWNER}&n=500", gerrit=True)
    numbers = sorted({c["_number"] for c in found} | {int(n) for n in CL_RE.findall(status)})
    changes = [change_record(fetch_json(f"{GERRIT}/changes/{n}?o=MESSAGES", gerrit=True)) for n in numbers]
    return issues, changes


def main(argv=None):
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--offline", action="store_true", help="refresh the git part only")
    ap.add_argument("--as-of", default=datetime.date.today().isoformat(), help="snapshot date (YYYY-MM-DD)")
    ap.add_argument("--output", default=str(OUTPUT))
    a = ap.parse_args(argv)
    if a.offline:
        old = json.loads(Path(a.output).read_text())
        issues, changes = old["issues"], old["changes"]
    else:
        issues, changes = upstream()
    snapshot = {"as_of": a.as_of, "git": git_series(), "issues": issues, "changes": changes}
    Path(a.output).write_text(json.dumps(snapshot, indent=1, ensure_ascii=False) + "\n")
    status = (ROOT / "docs" / "upstream-status.md").read_text()
    manifests = {p.stem: p.read_text() for p in sorted((ROOT / "findings").glob("*.yaml"))}
    TSV.write_text(upstream_tsv(issues, changes, cl_fixes(status), cited_by(manifests)))
    print(f"{a.output}: {len(snapshot['git'])} days, {len(issues)} issues, {len(changes)} changes", file=sys.stderr)


if __name__ == "__main__":
    main()
