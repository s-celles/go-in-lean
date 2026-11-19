#!/usr/bin/env python3
"""Tests for history.py (stdlib unittest, no network).

Run: python3 -I scripts/test_history.py
"""

import os
import sys
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

import history as h  # noqa: E402

CL = "[857741](https://go-review.googlesource.com/c/go/+/857741)"
STATUS = f"""\
| Upstream item | Item state | CL | CL state | Scope / note |
|---|---|---|---|---|
| [#36897](https://github.com/golang/go/issues/36897) | OPEN | none | — | x |
| [#82763](https://github.com/golang/go/issues/82763) | OPEN | {CL} | NEW | y |
| [#82763](https://github.com/golang/go/issues/82763) | OPEN | {CL} | NEW | repeat |
| [traefik/yaegi#1750](https://github.com/traefik/yaegi/issues/1750) | OPEN | none | — | z |
"""

PROPERTIES = """\
properties:
  - id: A
    status: proved_in_model
    history:
      - {"date": "2026-11-01", "status": "inconclusive"}
  - id: B
    status: known_issue
  - id: C
    status: "proved_in_model"
"""

LEAN = """\
theorem a : True := trivial
  theorem b : True := trivial
@[simp] theorem c : True := trivial
private lemma d : True := trivial
-- theorem commented : True := trivial
/-- theorem in a doc comment -/
def theoremLike := 1
"""


class ParseTests(unittest.TestCase):
    def test_issue_urls_are_unique_and_ordered(self):
        self.assertEqual(h.issue_urls(STATUS), [
            ("golang/go", 36897), ("golang/go", 82763), ("traefik/yaegi", 1750)])

    def test_property_counts(self):
        self.assertEqual(h.property_counts(PROPERTIES), (3, 2))
        self.assertEqual(h.property_counts(""), (0, 0))

    def test_declaration_count_skips_comments(self):
        self.assertEqual(h.declarations(LEAN), 4)

    def test_issue_record(self):
        api = {"user": {"login": "s-celles-bot"}, "created_at": "2026-11-02T10:00:00Z",
               "closed_at": "2026-11-05T01:00:00Z", "state": "closed"}
        self.assertEqual(h.issue_record(("golang/go", 82763), api), {
            "ref": "golang/go#82763", "url": "https://github.com/golang/go/issues/82763",
            "reported": True, "opened": "2026-11-02", "closed": "2026-11-05"})
        api = {"user": {"login": "someone"}, "created_at": "2020-01-30T00:00:00Z", "closed_at": None}
        self.assertEqual(h.issue_record(("golang/go", 36897), api)["reported"], False)
        self.assertIsNone(h.issue_record(("golang/go", 36897), api)["closed"])

    def test_change_record(self):
        change = {"_number": 858901, "status": "ABANDONED", "created": "2026-11-04 10:00:00.000000000",
                  "submitted": None, "subject": "s",
                  "messages": [{"date": "2026-11-04 10:00:00.000000000", "message": "Uploaded patch set 1."},
                               {"date": "2026-11-17 09:28:13.889000000", "message": "Abandoned\n\nSuperseded"}]}
        self.assertEqual(h.change_record(change), {
            "number": 858901, "url": "https://go-review.googlesource.com/c/go/+/858901",
            "status": "ABANDONED", "mailed": "2026-11-04", "merged": None, "abandoned": "2026-11-17"})
        change = {"_number": 1, "status": "MERGED", "created": "2026-11-02 08:00:00.000000000",
                  "submitted": "2026-11-05 12:00:00.000000000", "messages": []}
        self.assertEqual(h.change_record(change)["merged"], "2026-11-05")

    def test_daily_last_commit(self):
        log = "a 2026-11-01\nb 2026-11-01\nc 2026-11-03\n"
        self.assertEqual(h.daily_commits(log), [("2026-11-01", "b", 2), ("2026-11-03", "c", 1)])


if __name__ == "__main__":
    unittest.main()
