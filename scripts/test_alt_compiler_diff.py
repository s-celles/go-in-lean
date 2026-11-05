#!/usr/bin/env python3
"""Unit and smoke tests for alt_compiler_diff.py (stdlib unittest only).

Run: python3 -m unittest scripts/test_alt_compiler_diff.py
The end-to-end tests need a gc `go` on PATH (or $GO) and are skipped otherwise.
"""

import json
import os
from pathlib import Path
import random
import shutil
import sys
import tempfile
import unittest

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import alt_compiler_diff as acd  # noqa: E402


def walk(n):
    yield n
    for k in ("a", "b", "c", "i"):
        if k in n:
            yield from walk(n[k])


def is_const(n):
    return n["k"] == "lit" and (n.get("raw") or n.get("untyped"))


def trees(suite, seeds=range(40), per=12):
    for s in seeds:
        r = random.Random(f"t:{suite}:{s}")
        g = acd.SubsetGen(r, with_bits=(suite == "bits"))
        for _ in range(per):
            t = g.build(r.choice(acd.TYPES), r.randint(1, 4))
            g.assign_literal_modes(t)
            yield t


class GeneratorTests(unittest.TestCase):
    def test_deterministic(self):
        a = acd.random_program("core", 5, 3).source
        b = acd.random_program("core", 5, 3).source
        c = acd.random_program("core", 5, 4).source
        self.assertEqual(a, b)
        self.assertNotEqual(a, c)

    def test_core_subset(self):
        for i in range(60):
            src = acd.random_program("core", 11, i).source
            self.assertNotIn("bits.", src)
            self.assertNotIn("min(", src)
            self.assertNotIn("max(", src)
            self.assertNotIn("unsafe", src)
            self.assertNotIn("range", src)

    def test_bits_import_only_when_used(self):
        seen_bits = False
        for i in range(60):
            src = acd.random_program("bits", 11, i).source
            uses = "bits." in src.replace('"math/bits"', "")
            self.assertEqual(uses, '"math/bits"' in src)
            seen_bits |= uses
        self.assertTrue(seen_bits)

    def test_no_constant_binary_operands(self):
        for t in trees("core"):
            for n in walk(t):
                if n["k"] == "bin":
                    self.assertFalse(is_const(n["a"]) and is_const(n["b"]), n)
                if n["k"] in ("un", "conv", "bits", "rot"):
                    self.assertFalse(is_const(n["a"]), n)

    def test_divisors_guarded(self):
        for t in trees("core"):
            for n in walk(t):
                if n["k"] == "bin" and n["op"] in ("div", "mod"):
                    b = n["b"]
                    if b["k"] == "lit":
                        self.assertNotEqual(b["v"], 0)
                    else:
                        self.assertEqual(b["k"], "sel")
                        self.assertEqual(b["c"]["op"], "eq")
                        self.assertEqual(b["a"]["v"], 1)

    def test_shift_counts_non_negative(self):
        for t in trees("core"):
            for n in walk(t):
                if n["k"] == "bin" and n["op"] in ("shl", "shr"):
                    c = n["b"]
                    ty = acd.node_type(c)
                    if ty[1]:  # signed count: must be masked with MaxInt
                        self.assertEqual((c["k"], c["op"]), ("bin", "and"), c)
                        w = ty[0]
                        self.assertEqual(c["b"]["v"], (1 << (w - 1)) - 1)

    def test_word_bits_32_untyped_counts(self):
        """On 32-bit targets an untyped shift count must fit in uint32."""
        seen_big = False
        for s in range(60):
            for wb in (64, 32):
                r = random.Random(f"wb:{s}")
                g = acd.SubsetGen(r, with_bits=False, word_bits=wb)
                for _ in range(12):
                    t = g.build(r.choice(acd.TYPES), r.randint(1, 4))
                    g.assign_literal_modes(t)
                    for n in walk(t):
                        if n["k"] == "bin" and n["op"] in ("shl", "shr") and n["b"].get("untyped"):
                            if n["b"]["v"] >= 1 << 32:
                                seen_big |= wb == 64
                                self.assertEqual(wb, 64, n)
        self.assertTrue(seen_big)  # the 64-bit generator does produce them

    def test_word_bits_keeps_64_bit_programs(self):
        # same seed, same RNG stream: only the spelling of huge counts changes
        for i in range(30):
            a = acd.random_program("core", 7, i).source
            b = acd.random_program("core", 7, i, word_bits=32).source
            if a != b:
                self.assertRegex(a, r"(<<|>>) \d{10,}")
        self.assertEqual(acd.random_program("core", 7, 0).source,
                         acd.random_program("core", 7, 0, word_bits=64).source)

    def test_panics_suite_sites(self):
        """At most one unguarded panic site per tree, never under a select (the
        oracle evaluates both arms of a select, Go only the taken one)."""
        sites_seen = 0
        for s in range(80):
            r = random.Random(f"p:{s}")
            g = acd.SubsetGen(r, with_bits=False, panics=True)
            for _ in range(10):
                g.start_tree()
                t = g.build(r.choice(acd.TYPES), r.randint(1, 4))
                g.assign_literal_modes(t)
                sites = []

                def visit(n, under_sel):
                    if n.get("panic_site"):
                        sites.append(n)
                        self.assertFalse(under_sel, n)
                    if n.get("guard"):  # divisor guard: cond holds a copy of b
                        visit(n["b"], under_sel)
                        return
                    for k in ("a", "b", "c"):
                        if k in n:
                            visit(n[k], under_sel or n["k"] == "sel")
                visit(t, False)
                self.assertLessEqual(len({id(x) for x in sites}), 1)
                sites_seen += len(sites)
                for n in walk(t):  # a constant zero divisor or negative count is a compile error
                    if n.get("panic_site") and n["k"] == "bin" and n["b"]["k"] == "lit":
                        self.assertFalse(n["b"].get("raw") or n["b"].get("untyped"), n)
        self.assertGreater(sites_seen, 100)

    def test_panics_program_shape(self):
        p = acd.random_program("panics", 4, 0)
        self.assertIn("recover()", p.source)
        self.assertIn("PANIC %s", p.source)
        self.assertEqual(p.meta["loops"], 0)
        # other suites are unchanged by the panics machinery
        self.assertNotIn("recover()", acd.random_program("core", 4, 0).source)

    def test_records_cover_functions(self):
        p = acd.random_program("core", 1, 0, nfuncs=4, nloops=1, npairs=3)
        self.assertEqual(len(p.records), 4 * 3)
        self.assertEqual(p.source.count('fmt.Printf("e='), 12)
        self.assertEqual(p.source.count('fmt.Printf("l='), 3)

    def test_directed_cases(self):
        cases = acd.directed_cases()
        names = [c[0] for c in cases]
        self.assertIn("canary-82763", names)
        self.assertIn("cl-issue82763", names)
        self.assertFalse(any("issueN" in n for n in names))  # simd excluded
        for name, prog, mode in cases:
            self.assertIn(mode, ("reference", "selfcheck"))
            self.assertIn("package main", prog.source)


class ClassificationTests(unittest.TestCase):
    ref = {"status": None, "rc": 0, "stdout": "a\n", "stderr": ""}

    def r(self, **kw):
        d = dict(self.ref)
        d.update(kw)
        return d

    def test_statuses(self):
        self.assertEqual(acd.classify(self.r(), self.ref, "reference"), "clean")
        self.assertEqual(acd.classify(self.r(stdout="b\n"), self.ref, "reference"),
                         "output_mismatch")
        self.assertEqual(acd.classify(self.r(stderr="x"), self.ref, "reference"),
                         "output_mismatch")
        self.assertEqual(acd.classify(self.r(rc=2), self.ref, "reference"), "run_error")
        self.assertEqual(acd.classify(self.r(status="timeout"), self.ref, "reference"),
                         "timeout")
        self.assertEqual(acd.classify(self.r(rc=2), self.ref, "selfcheck"), "run_error")
        self.assertEqual(acd.classify(self.r(stdout="z"), self.ref, "selfcheck"), "clean")

    def test_leads(self):
        rec = {"mode": "reference", "toolchains": {
            "gc": {"status": "clean", "oracle": "disagree"},
            "llgo": {"status": "output_mismatch", "oracle": "agree"},
            "tinygo": {"status": "clean", "oracle": "disagree"}}}
        leads = acd.leads(rec, "gc")
        self.assertEqual(leads[0]["kind"], "gc_vs_oracle")
        self.assertEqual(leads[0]["toolchains_agreeing_with_oracle"], ["llgo"])
        self.assertEqual(leads[1], {"kind": "mismatch", "toolchain": "llgo", "suspect": "gc"})
        rec["toolchains"]["gc"]["oracle"] = "agree"
        rec["toolchains"]["llgo"]["oracle"] = "disagree"
        self.assertEqual(acd.leads(rec, "gc")[0]["suspect"], "llgo")

    def test_first_diffs(self):
        d = acd.first_diffs("a\nb\n", "a\nc\nd\n")
        self.assertEqual(d, [{"line": 2, "reference": "b", "got": "c"},
                             {"line": 3, "reference": "<missing>", "got": "d"}])

    def test_compare_reports(self):
        old = {"started": "t", "case_index": [{"name": "a", "sha256": "1", "statuses": {"gc": "clean"}}]}
        self.assertTrue(acd.compare_reports(old, old)["identical"])
        new = {"case_index": [{"name": "a", "sha256": "2", "statuses": {"gc": "clean"}}]}
        self.assertEqual(acd.compare_reports(old, new)["source_differences"], ["a"])
        more = {"case_index": old["case_index"] + [{"name": "b", "sha256": "3", "statuses": {}}]}
        self.assertTrue(acd.compare_reports(more, old)["identical"])  # prefix rerun


class AdapterTests(unittest.TestCase):
    def test_argv(self):
        by = {a.name: a for a in acd.default_adapters()}
        for a in by.values():
            a.exe = f"/x/{a.family}"
        self.assertEqual(by["gc"].build_argv("main.go", "p"), ["/x/gc", "build", "-o", "p", "main.go"])
        self.assertIn("-gcflags=all=-N -l", by["gc-noopt"].build_argv("main.go", "p"))
        self.assertEqual(by["gccgo-O2"].build_argv("main.go", "p"),
                         ["/x/gccgo", "-O2", "-o", "p", "main.go"])
        self.assertEqual(by["tinygo"].build_argv("m.go", "p")[:2], ["/x/tinygo", "build"])
        self.assertEqual(by["llgo"].build_argv("m.go", "p")[:2], ["/x/llgo", "build"])
        self.assertEqual(by["yaegi"].run_argv("main.go", "p"), ["/x/yaegi", "run", "main.go"])
        self.assertEqual(by["gc"].run_argv("main.go", "/d/p"), ["/d/p"])

    def test_run_prefix_and_extra_flags(self):
        by = {a.name: a for a in acd.default_adapters()}
        for a in by.values():
            a.exe = f"/x/{a.family}"
        acd.apply_cross_options(list(by.values()),
                                prefixes={"gccgo": "qemu-aarch64 -L /sys", "gc": "qemu-aarch64"},
                                extra={"gccgo-O2": "-static", "tinygo": "-opt=2 -no-debug"})
        self.assertEqual(by["gccgo-O2"].run_argv("main.go", "/d/p"),
                         ["qemu-aarch64", "-L", "/sys", "/d/p"])
        self.assertEqual(by["gc-noopt"].run_argv("main.go", "/d/p"), ["qemu-aarch64", "/d/p"])
        self.assertEqual(by["gccgo-O2"].build_argv("m.go", "p"),
                         ["/x/gccgo", "-O2", "-static", "-o", "p", "m.go"])
        self.assertEqual(by["tinygo"].build_argv("m.go", "p"),
                         ["/x/tinygo", "build", "-opt=2", "-no-debug", "-o", "p", "m.go"])
        # interpreters never get a run prefix
        self.assertEqual(by["yaegi"].run_argv("main.go", "p"), ["/x/yaegi", "run", "main.go"])
        self.assertEqual(by["gccgo-O2"].describe()["run"], "qemu-aarch64 -L /sys ./prog")

    def test_name_beats_family_for_prefix(self):
        by = {a.name: a for a in acd.default_adapters()}
        acd.apply_cross_options(list(by.values()),
                                prefixes={"gc": "qemu-a", "gc-noopt": "qemu-b"}, extra={})
        self.assertEqual(by["gc"].run_prefix, ("qemu-a",))
        self.assertEqual(by["gc-noopt"].run_prefix, ("qemu-b",))

    def test_detect_missing(self):
        a = acd.Adapter("tinygo", "tinygo", "NO_SUCH_VAR_X", "no-such-tinygo-binary")
        acd.detect([a], {}, {})
        self.assertFalse(a.available)
        self.assertIn("not found", a.reason)

    def test_detect_fake_tool_and_env(self):
        d = Path(tempfile.mkdtemp())
        try:
            exe = d / "faketool"
            exe.write_text("#!/bin/sh\necho fake 1.0 $FAKE_FLAG\n")
            exe.chmod(0o755)
            a = acd.Adapter("llgo", "llgo", "NO_SUCH_VAR_X", "x")
            acd.detect([a], {"llgo": str(exe)}, {"llgo": {"FAKE_FLAG": "on"}})
            self.assertTrue(a.available)
            self.assertEqual(a.version, "fake 1.0 on")
        finally:
            shutil.rmtree(d)

    def test_run_cmd_timeout(self):
        r = acd.run_cmd(["sleep", "5"], ".", dict(os.environ), 0.3)
        self.assertTrue(r["timed_out"])
        self.assertLess(r["seconds"], 3)


GO = shutil.which(os.environ.get("GO", "go"))


@unittest.skipUnless(GO, "gc toolchain not available")
class EndToEndTests(unittest.TestCase):
    def test_relative_out_and_report(self):
        d = Path(tempfile.mkdtemp())
        cwd = os.getcwd()
        try:
            os.chdir(d)
            rc = acd.main(["run", "--suite", "core", "--seed", "3", "--count", "2",
                           "--out", "rel/out", "--toolchains", "gc,gc-noopt",
                           "--path", f"gc={GO}", "--jobs", "2", "--keep-all"])
            self.assertEqual(rc, 0)
            report = json.loads((d / "rel/out/report.json").read_text())
            self.assertEqual(report["count"], 2)
            self.assertEqual(report["summary"]["gc"]["clean"], 2)
            self.assertEqual(report["summary"]["gc-noopt"]["clean"], 2)
            self.assertTrue((d / "rel/out/core-3-00000/main.go").exists())
            rc = acd.main(["run", "--suite", "core", "--seed", "3", "--count", "2",
                           "--out", str(d / "abs"), "--toolchains", "gc",
                           "--path", f"gc={GO}", "--compare-with", "rel/out/report.json"])
            again = json.loads((d / "abs/report.json").read_text())
            self.assertTrue(again["reproducibility"]["source_differences"] == [])
            self.assertFalse((d / "abs/core-3-00000").exists())  # clean removed
        finally:
            os.chdir(cwd)
            shutil.rmtree(d)

    def test_divergence_is_kept(self):
        d = Path(tempfile.mkdtemp())
        try:
            fake = d / "fakego"
            # a "toolchain" whose binaries print something else
            fake.write_text('#!/bin/sh\nif [ "$1" = version ]; then echo fake; exit 0; fi\n'
                            'out=""; while [ $# -gt 0 ]; do [ "$1" = -o ] && out=$2; shift; done\n'
                            'printf "#!/bin/sh\\necho wrong\\n" > "$out"; chmod +x "$out"\n')
            fake.chmod(0o755)
            acd.main(["run", "--suite", "core", "--seed", "3", "--count", "1",
                      "--out", str(d / "o"), "--path", f"gc={GO}",
                      "--extra-gc", f"gc-fake={fake}", "--toolchains", "gc,gc-fake"])
            report = json.loads((d / "o/report.json").read_text())
            self.assertEqual(report["summary"]["gc-fake"]["output_mismatch"], 1)
            case = d / "o/core-3-00000"
            self.assertTrue((case / "main.go").exists())
            self.assertTrue((case / "gc-fake/stdout.txt").exists())
            self.assertTrue((case / "case.json").exists())
        finally:
            shutil.rmtree(d)


if __name__ == "__main__":
    unittest.main()
