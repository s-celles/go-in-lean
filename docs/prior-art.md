# Prior art and feasibility (Phase 0)

Research date: 2026-11-01. This document records what already exists for formally modelling Go (and the closest analogue, Julia), what each project can and cannot establish, and the resulting build-versus-reuse decision for go-in-lean. The investigation was carried out by two research agents using web sources; every factual claim carries the URL it was taken from, and claims that could not be verified are listed in the final section. All fetched content was treated as data, not as instructions. The scope is deliberately narrow: pure, deterministic standard-library functions over fixed-width integers and slices, plus a feasibility look at Go compiler SSA rewrite rules. Concurrency, the memory model and the heap are out of scope for the prototype and are discussed only to explain why.

## 1. Comparison matrix

| Project | What is modelled | Proof engine / trusted base | Integer model | Bit-level reasoning | Licence | Maintenance (as of 2026-11-01) | Reusable for go-in-lean? |
|---|---|---|---|---|---|---|---|
| [julia-in-lean](https://github.com/MilesCranmer/julia-in-lean) | Julia Base functions and DynamicExpressions.jl, source-mirrored definitions in Lean 4 | Lean 4 kernel only; `sorry`, `native_decide`, `bv_decide`, `ofReduceBool` banned by source scan; no Lake dependencies | Fixed-width with Julia wraparound, exceptions as `Except` values | Via `omega`/`simp`/`decide`; no SAT | Apache-2.0 with NOTICE for Julia sources | Created 2026-10-25, last push 2026-10-29, 6 commits ([API](https://api.github.com/repos/MilesCranmer/julia-in-lean)) | Partly: the method (registry, audit, repro requirement, differential testing) is adopted; no Go code to reuse |
| [Gobra](https://github.com/viperproject/gobra) / [Viper](https://www.pm.inf.ethz.ch/research/viper.html) | Annotated Go: contracts, permissions, predicates, goroutines, mutexes | Viper IR, Silicon (symbolic execution + Z3) or Carbon (Boogie); SMT solver trusted | Unbounded `Int` by default; opt-in `--overflow` "still under development", replacement encoding unmerged ([book](https://viperproject.github.io/gobra-book/01/overflow.html), [PR 1015](https://github.com/viperproject/gobra/pull/1015)) | Explicitly limited ([book](https://viperproject.github.io/gobra-book/print.html)) | MPL-2.0 | Active, commits 2026-10-30 ([commits](https://github.com/viperproject/gobra/commits/master)) | No: wrong integer model for overflow bugs, no generics, SMT in trusted base |
| [Goose](https://github.com/goose-lang/goose) / [Perennial](https://github.com/mit-pdos/perennial) (Rocq `master`, Lean 4 `lean` branch) | Translation of a Go subset to GooseLang (HeapLang-style), Iris program logic, crash safety | Rocq + Iris, or Lean 4 + iris-lean (`lean` is now the primary branch, [README](https://raw.githubusercontent.com/mit-pdos/perennial/lean/README.md)) | 64-bit unsigned words in GooseLang ([notes](https://tchajed.github.io/sys-verif-fa24/notes/goose.html)) | Through word operations in the language model | Perennial MIT (`master`); `lean` branch licence not retrievable; goose MIT | goose archived 2026-04-07; Perennial `lean` commits on 2026-11-01 | Partly: complementary separation-logic stack; revisit for heap/aliasing functions; not reused in the prototype |
| Featherweight Go ([arXiv](https://arxiv.org/abs/2005.11710)) | Core calculus: structs, interfaces, method dispatch, generics (FGG) | Pen-and-paper proofs; Go-implemented checkers with dynamic tests ([artifact](https://zenodo.org/record/4048298)) | Not the focus | None | Paper; prototype code at [templatek/fgg](https://github.com/templatek/fgg) | Academic artefact, 2020 | No: no mechanisation found, no integer semantics |
| K-Go ([listing](https://www.aminer.org/pub/648caf5dd68f896efa6a94ba/k-go-an-executable-formal-semantics-of-go-language-in-k-framework)) | Executable semantics of Go 1.18 in K: types, expressions, concurrency, channels | K framework | Unknown (paper not available) | Unknown | Unknown; repository not found | 2023 paper, no public artefact found | No: nothing to download |
| [Gomela](https://github.com/nicolasdilley/gomela) | Channel concurrency extracted to Promela for Spin | Spin bounded model checking | Not modelled | None | No licence field ([API](https://api.github.com/repos/nicolasdilley/Gomela)) | Last push 2023-05-31 | No: concurrency only |
| [golang_tv](https://github.com/ryan-berger/golang_tv) (Alive2 for Go) | Lifts Go SSA to LLVM IR and checks rewrites with Alive2 | Alive2 + Z3 (SMT trusted) | LLVM fixed-width | Yes (SMT bit-vectors) | Not stated in report | "In its infancy", 11 commits; panics unsupported | No: abandoned; but confirms the gap for Phase 6 |
| Go's own testing | Native fuzzing ([doc](https://go.dev/doc/security/fuzz/)), race detector ([doc](https://go.dev/doc/articles/race_detector)), `test/codegen` asmcheck, `test/fixedbugs`, `cmd/compile/internal/test` constFold/divconst/shift tests ([dir](https://go.dev/src/cmd/compile/internal/test/)) | Execution, no proofs | Real machine semantics | Real machine semantics | BSD-3-Clause | Maintained with Go | Yes: oracles, seed corpora and regression tests |
| Lean 4 core (`BitVec`, `bv_decide`, `omega`, `decide`) | Fixed-width bit-vectors with SMT-LIB-complete operations ([API](https://lean-lang.org/doc/api/Init/Data/BitVec/Basic.html)) | Lean kernel; `bv_decide` adds `Lean.ofReduceBool` (verified LRAT checker run natively) ([4.12 notes](https://lean-lang.org/doc/reference/latest/releases/v4.12.0/)) | Fixed-width, truncating `sdiv`/`srem`, division by zero returns 0 | Yes (bit-blasting to CaDiCaL) | Apache-2.0 | Lean 4.35.0 stable 2026-10-12 ([releases](https://lean-lang.org/doc/reference/latest/releases/)) | Yes: the semantic substrate and the proof automation |
| [Plausible](https://github.com/leanprover-community/plausible) | QuickCheck-style property testing for Lean | Random testing, no proof | n/a | n/a | Apache-2.0 | Pushed 2026-10-27, toolchain v4.36.0-rc2 | Not now: adds a dependency; Go fuzzing and `decide` cover the need |

## 2. Per-project notes

### 2.1 julia-in-lean

Architecture ([README](https://github.com/MilesCranmer/julia-in-lean), [Discourse](https://discourse.julialang.org/t/formalizing-julia-in-lean-and-finding-400-bugs-in-base/140243)):

- Source-mirrored models: each Julia function gets a Lean definition that follows the source line by line, with the same branch order and integer wraparound; exceptions are `Except JlError α` values; unchecked memory accesses are modelled explicitly.
- Properties are hand-written closed `Prop`s derived from docstrings and manual statements; an automated "generality count" rejects statements that only check examples. There is no automated theorem generation.
- A proven entry is a theorem whose type is exactly the property; a refuted entry is a theorem whose type is exactly the negation, built from a concrete counterexample and checked with `decide`. `Registry.lean` produces `registry.tsv`; `Audit.lean` fails the build on duplicate ids, unsettled entries, mismatched theorem types, non-standard axioms, or missing quantified variables.
- Every Lean counterexample needs a pure-Julia reproducer `repro/<id>.jl` whose last line prints `REPRODUCED <id>`; a counterexample without a reproducer is treated as a model bug. Reproducers run on Julia 1.13.2 and a pinned master.
- Differential testing precedes proving: an exhaustive 656,896-row Int8/UInt8 table, 236,954 Float64 operations on two Julia versions, about 15,000 TOML documents. "When the model and Julia disagree, the model is wrong until shown otherwise."
- Toolchain `leanprover/lean4:v4.34.1`, no Lake dependencies, `-M8000` memory cap ([lakefile](https://raw.githubusercontent.com/MilesCranmer/julia-in-lean/main/julia-base/lakefile.toml)). A source scan rejects `sorry`, `admit`, `native_decide`, `bv_decide` and `ofReduceBool` because each "bypasses or weakens the kernel check" ([README](https://raw.githubusercontent.com/MilesCranmer/julia-in-lean/main/README.md)). Tactics in use: `simp`, `omega`, `cases`, `decide`, core `Int` lemmas.

Bug counts, claimed versus filed versus confirmed:

- Discourse post (2026-10-25): "about 400 (!) bugs in Base", 75 manually filtered ones filed, cost about $5,000 of API usage ([thread](https://discourse.julialang.org/t/formalizing-julia-in-lean-and-finding-400-bugs-in-base/140243.md)).
- README (2026-10-29): 6,452 registry entries (5,058 proven, 560 refuted, 834 todo); 627 bug write-ups; "107 issues filed on JuliaLang/julia"; two security-relevant ones held back; 38 fix PRs merged for DynamicExpressions.jl.
- Independent GitHub API check (2026-11-01): 108 issues by `MilesCranmerBot`, 33 labelled `bug`, 27 closed as `completed`, 0 closed as `not_planned`; 109 PRs, 45 merged ([issues](https://api.github.com/search/issues?q=repo:JuliaLang/julia+author:MilesCranmerBot+is:issue), [merged PRs](https://api.github.com/search/issues?q=repo:JuliaLang/julia+author:MilesCranmerBot+is:pr+is:merged)). Reading: confirmed lower bound about 27 to 45, filed 108, claimed 400 to 627 depending on the unit counted.
- No fraction of real bugs versus intended behaviour is published; a `maybe_intended` field marks inferred invariants, and the author says "a fair number of findings are of that kind". Maintainers pushed back on several (e.g. `LinRange` exactness #64272, `tanh` monotonicity #64225).

Lessons stated by the author: of 130 first-pass memory-safety "proofs", review failed 128 that had assumed their conclusion ("hollow proofs"), which the audit cannot catch; reproducer harness false negatives; internal-helper bugs unreachable from the public API were withdrawn; agents under time pressure stub definitions or narrow statements; start with one small module, set up differential tests and audit first.

### 2.2 Gobra and Viper

- Contracts (`requires`, `ensures`, `preserves`, `invariant`, `decreases`), fractional permissions, predicates, pure and ghost code, quantifiers with triggers, interfaces with implementation proofs ([book](https://viperproject.github.io/gobra-book/print.html)). CAV 2021 paper ([arXiv](https://arxiv.org/abs/2105.13840)).
- Integers: historically unbounded Viper `Int`s with overflow checking as a separate transformation ([PR 960](https://github.com/viperproject/gobra/pull/960)). "By default, Gobra performs no overflow checking"; `--overflow` is "still under development" ([book](https://viperproject.github.io/gobra-book/01/overflow.html)). The maintainer called the old transformation "fundamentally broken"; the replacement bounded encoding ([PR 1015](https://github.com/viperproject/gobra/pull/1015)) is an open draft with bitwise reasoning not yet supported.
- No generics; no range over integers/strings/functions; `delete`/`clear` unsupported ([book](https://viperproject.github.io/gobra-book/print.html)). Standard library handled by spec-only stubs ([stubs](https://github.com/viperproject/gobra/tree/master/src/main/resources/stubs)).
- Concurrency: permission transfer at `go`, mutex invariants, static race freedom. Verified SCION router data plane (about 4,700 lines) ([repo](https://github.com/viperproject/VerifiedSCION), [paper](https://arxiv.org/html/2405.06074v1)), archived 2026-10-20. No Gobra verification of Go standard library implementations was found.

### 2.3 Goose and Perennial

- goose-lang/goose archived 2026-04-07, MIT; development moved to mit-pdos/perennial ([API](https://api.github.com/repos/goose-lang/goose)). Classic Goose: single-assignment variables, heap pointers for mutation, slices as contiguous heap cells, `go f()` as fork, 64-bit unsigned words; output is GooseLang, correctness criterion behaviour(p) ⊆ semantics(goose(p)) checked by differential tests ([notes](https://tchajed.github.io/sys-verif-fa24/notes/goose.html)).
- Perennial's default branch is now `lean`: "Perennial's goose framework and program proofs, in Lean 4 on top of iris-lean", toolchain v4.34.1, dependencies iris-lean, batteries, Qq; two end-to-end panic-freedom examples, `sync.RWMutex` proofs, trusted hand-written models for `sync.Pool` and `strings.Join` (the latter omits a reachable overflow panic) ([README](https://raw.githubusercontent.com/mit-pdos/perennial/lean/README.md), [manifest](https://raw.githubusercontent.com/mit-pdos/perennial/lean/lake-manifest.json)). iris-lean is Apache-2.0 ([API](https://api.github.com/repos/leanprover-community/iris-lean)).
- No other Go-in-Lean-4 project was found ([search](https://api.github.com/search/repositories?q=golang+semantics+lean4&sort=updated)).

### 2.4 Other Go semantics

- Featherweight Go: pen-and-paper progress/preservation and a bisimulation with monomorphisation; no proof-assistant mechanisation found ([arXiv](https://arxiv.org/abs/2005.11710)).
- K-Go: IET Blockchain 2023, Go 1.18, claims 100% coverage of the official test suite; no repository or licence found.
- Isabelle/HOL: an AFP entry for Isabelle-to-Go code generation, explicitly not a Go semantics ([AFP](https://www.isa-afp.org/entries/Go.html)); a 2024 PhD call for a Go semantics with no published result.
- Go memory model: prose plus relations ([spec](https://go.dev/ref/mem)); paper-level operational semantics by Fava et al. ([pdf](https://dfava.github.io/papers/fava2018operational.pdf)), not mechanised.
- Gomela and behavioural types ("Fencing off Go", [KAR](https://kar.kent.ac.uk/62218)) target channel concurrency only.

### 2.5 Go's own testing infrastructure

- Native fuzzing since Go 1.18: `FuzzXxx(f *testing.F)`, seed corpus, failing inputs saved under `testdata/fuzz` ([doc](https://go.dev/doc/security/fuzz/)).
- Race detector finds only races that execute ([doc](https://go.dev/doc/articles/race_detector)).
- `test/codegen` asmcheck comments, `test/fixedbugs/issueNNNNN.go` regressions, e.g. issue15175 on unsigned shift sign-extension ([file](https://raw.githubusercontent.com/golang/go/master/test/fixedbugs/issue15175.go)).
- SSA rewrite rules: `cmd/compile/internal/ssa/_gen/*.rules`, syntax `sexpr [&& cond] => sexpr`, first matching rule in file order wins, rulegen rejects duplicates and shadowing ([rulegen](https://raw.githubusercontent.com/golang/go/master/src/cmd/compile/internal/ssa/_gen/rulegen.go)). Example rules: `(Add64 (Const64 [c]) (Const64 [d])) => (Const64 [c+d])`; `((Lsh64|Rsh64U)x64 _ (Const64 [c])) && uint64(c) >= 64 => (Const64 [0])`; `(Div64u n (Const64 [c])) && isPowerOfTwo(c) => (Rsh64Ux64 n (Const64 [log64(c)]))` ([generic.rules](https://raw.githubusercontent.com/golang/go/master/src/cmd/compile/internal/ssa/_gen/generic.rules)). `rewrite_test.go` tests helper functions, not rule semantics ([file](https://go.dev/src/cmd/compile/internal/ssa/rewrite_test.go)); execution tests live in `cmd/compile/internal/test` (constFold, divconst, shift, mulconst, truncconst).
- Verification of rules: a 2023 golang-dev thread proposed Alive-style checking; the compiler team declined to expose internals but allowed copying the package ([thread](https://groups.google.com/g/golang-dev/c/7u7aV93qvm8)); golang_tv and [mmcloughlin/ssarules](https://github.com/mmcloughlin/ssarules) are incomplete experiments. No merged or published verification of generic.rules was found.
- `math/bits`: de Bruijn `TrailingZeros`, SWAR `OnesCount64`, 8-bit tables generated by `make_tables.go`, `Div64` panics via `//go:linkname` to runtime errors ([bits.go](https://raw.githubusercontent.com/golang/go/master/src/math/bits/bits.go)); `Add64` carry input "must be 0 or 1; otherwise the behavior is undefined" ([#54255](https://github.com/golang/go/issues/54255) closed as not a bug).

### 2.6 Alive2 and historical Go miscompiles

- Alive2 (PLDI 2021): bounded translation validation for LLVM, refinement with undefined behaviour, 47 LLVM bugs ([pdf](https://www-old.cs.utah.edu/~regehr/alive2-pldi21.pdf), [repo](https://github.com/AliveToolkit/alive2), MIT).
- GoSmith (2014): 31 gc, 18 gccgo, 5 llgo bugs by differential testing ([thread](https://groups.google.com/g/golang-dev/c/kbpzxu69BcY)).
- Rewrite-rule bug classes: [#15175](https://github.com/golang/go/issues/15175) unsigned shift constant folding (Go 1.7); [#32711](https://github.com/golang/go/issues/32711) mergePoint in rules; [#42753](https://github.com/golang/go/issues/42753) 32-bit AuxInt sign extension; [#57184](https://github.com/golang/go/issues/57184) arm64 CondSelect bool upper bits broke `sort.SliceStable`; [#59468](https://github.com/golang/go/issues/59468) amd64 LEA late-lower; [#64285](https://github.com/golang/go/issues/64285) riscv64 large shifts; [#64715](https://github.com/golang/go/issues/64715) arm assembler shift-by-0; [#79886](https://github.com/golang/go/issues/79886) arm64 `Rsh...x32` upper-half garbage (2026); commit [8dcb3171](https://go.googlesource.com/go/+/8dcb3171f650e2f8fe68302cae0d6bf78b2e544a) shift canonicalisation gave `Const64` a 4-byte type. Recurring themes: shift-amount width and sign, AuxInt sign-extension invariants, bool upper bits, over-general per-arch lowering.

### 2.7 Known stdlib correctness issues (regression oracle)

| Issue | Summary | Fixed |
|---|---|---|
| [#16237](https://github.com/golang/go/issues/16237) | `strings`/`bytes.Repeat`: `len*count` overflow gave a short result | Go 1.8 |
| [#60138](https://github.com/golang/go/issues/60138) | `slices.Insert`/`Replace` wrong when inserted values alias the slice | Go 1.21 |
| [#63913](https://github.com/golang/go/issues/63913) / [#64152](https://github.com/golang/go/issues/64152) | `slices.Insert` did not panic on out-of-range index with no values | Nov 2023 |
| [#56700](https://github.com/golang/go/issues/56700) | x/exp `slices.Replace` did not panic for i > j | Nov 2022 |
| [#63393](https://go.dev/issue/63393) | `Delete`/`Compact`/`Replace` now clear the tail (semantic change) | Go 1.22 |
| [#52518](https://github.com/golang/go/issues/52518) | pdqsort with NaN breaks strict weak order; resolved by documentation | Apr 2022 |
| [#70144](https://github.com/golang/go/issues/70144) | `slices` xorshift used 32-bit constants on uint64 | Go 1.24 |
| [#56457](https://github.com/golang/go/issues/56457) | `strings.Index` wrong on ppc64le/power9 (bytealg) | Oct 2022 |
| [#54255](https://github.com/golang/go/issues/54255) | `Add64` with carry 2: not a bug, precondition violated | n/a |

No confirmed wrong-result bug in pure-Go `math/bits` or `sort.Search` was found ([#34827](https://golang.org/issue/34827), [#37869](https://golang.org/issue/37869) were user errors).

## 3. Answers to the Phase 0 questions

1. **Which Go behaviours already have formal models?** Channel concurrency (Gomela, behavioural types), a core object calculus (Featherweight Go, on paper), a GooseLang translation of a heap-and-goroutine subset with 64-bit words (Goose/Perennial, Rocq and Lean 4), a K-framework semantics with no public artefact (K-Go), and Gobra's Viper encoding with unbounded integers. None provides an executable, kernel-checked, bit-precise model of Go standard-library code suitable for refutation by counterexample.

2. **Which components can be reused?** Lean core `BitVec` (SMT-LIB-complete operations, truncating signed division matching Go's `/` and `%`), `bv_decide`, `omega`, `decide`; Go's native fuzzing, `test/codegen` and `cmd/compile/internal/test` corpora as oracles; the GitHub issue history as a regression oracle and bug-class catalogue; julia-in-lean's process design (registry, audit, reproducer rule, differential tests first).

3. **Which guarantees can existing tools establish?** Gobra proves memory safety, crash safety, race freedom and user contracts under an unbounded-integer model, with the SMT solver trusted. Perennial-lean proves panic freedom and crash/distributed adequacy for heap programs under Iris, with iris-lean and the Goose translator trusted. Go's own tests establish behaviour on executed inputs only. Alive2-style tools do not exist in working form for Go.

4. **What would Lean 4 add?** Exact fixed-width semantics with a small trusted base (kernel plus, for `bv_decide`, a verified LRAT checker), executable models that can be differentially tested against the real toolchain, kernel-checked refutations (`decide` on a concrete counterexample), and one language for model, specification and proof. Lean 4.35.0 bundles independent kernel checkers and `lake check` privilege separation ([release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)).

5. **Where would a new Go-to-Lean translation introduce unacceptable complexity?** Anywhere heap aliasing, goroutines, channels, `unsafe`, reflection, `defer`/`recover`, or the memory model matter. `slices.Insert`/`Replace` already depend on pointer-overlap checks (`overlaps`, `startIdx`) that a list model cannot express; a faithful treatment needs a heap model such as GooseLang. Also: `int`/`uint` width is implementation-defined, compiler intrinsics replace the pure-Go `math/bits` code on major architectures, and floating point was deliberately left out.

6. **Can existing verified Go fragments or specifications be reused rather than recreated?** Not for the chosen targets. Gobra's stdlib support is spec-only stubs; Perennial-lean's hand-written models cover a few packages (`sync.Pool`, `strings.Join`) and are trusted rather than verified; no verified `math/bits`, `slices`, `sort`, `strings` or `bytes` code exists in any proof assistant. Reuse is therefore limited to oracles (Go tests, issues) and infrastructure (Lean core).

7. **Is Lean the appropriate proof engine per target?** Pure integer and bit functions in `math/bits`: yes, `BitVec` plus `bv_decide` fit exactly, with the caveat that general 32- and 64-bit multiplication can exceed SAT budgets. List-like `slices`/`sort` functions: yes, standard inductive proofs over `List`. Aliasing-sensitive `slices.Insert`/`Replace`: only with a heap model; a separation-logic stack (Perennial-lean) is better suited, so the prototype restricts itself to the non-aliasing contract. Concurrency: no, out of scope; Gobra, Gomela or Perennial are the right tools. Compiler SSA rewrite rules: yes for the generic arithmetic rules (each rule is a fixed-width equivalence under a side condition), which is precisely the bug class seen in #15175, #64285, #79886 and commit 8dcb3171; architecture-specific lowering needs machine semantics and is out of scope.

## 4. Licensing considerations

- Go sources are BSD-3-Clause. The transcribed lookup tables and line-by-line transliterations in `GoInLean/Stdlib` are derivative works; Go's LICENSE notice is kept in a `NOTICE` file, following julia-in-lean's treatment of Julia sources.
- Gobra: MPL-2.0 ([repo](https://github.com/viperproject/gobra)). Perennial: MIT on `master` ([LICENSE](https://raw.githubusercontent.com/mit-pdos/perennial/master/LICENSE)); the `lean` branch licence could not be retrieved. iris-lean: Apache-2.0. julia-in-lean: Apache-2.0 with NOTICE. Alive2: MIT. Lean 4: Apache-2.0.
- This repository: MIT, chosen for the prototype for simplicity. The user may prefer Apache-2.0 (patent grant, alignment with Lean and julia-in-lean); nothing in the code base depends on the choice.

## 5. Build-versus-reuse decision

**Build.** A small, dependency-free Lean 4 model library for the bounded subset: fixed-width integers as core `BitVec`, slices as lists, panics as `Except` values. The method is julia-in-lean's: source-mirrored definitions, a property registry with an axiom audit, differential testing of the model against the pinned Go toolchain before any proof is trusted, and a Go reproducer for every refutation. Reason: no existing project offers executable, kernel-checked, bit-precise semantics of Go standard-library code in Lean 4.

**Reuse.**

- Lean core `BitVec` semantics and the `bv_decide`, `omega`, `decide` tactics. No Mathlib: the project has zero Lake dependencies, which keeps CI fast and the trusted base small.
- Go's own test corpus and native fuzzing as oracles for the Go side.
- Known golang/go issues as regression oracles and as the catalogue of bug classes to target: #16237 (Repeat overflow), #60138 (Insert/Replace aliasing), #63913/#64152 (Insert bounds), #54255 (Add64 carry precondition), #57184, #15175, #64285, #79886 and commit 8dcb3171 (shift canonicalisation miscompile).

**Not reused, and why.**

- Gobra: unbounded-integer model, experimental overflow mode, no generics, no bit-level reasoning, SMT solver in the trusted base.
- Goose/Perennial-lean: a separation-logic weakest-precondition stack for heap and concurrent programs with a heavyweight iris-lean dependency. Complementary rather than competing; to be revisited for aliasing-sensitive slice functions.
- K-Go: no public artefact found.
- golang_tv and ssarules: abandoned experiments. They confirm that no verified Go SSA rewrite rules exist, so Phase 6 targets a genuine gap.

**Deviation from julia-in-lean.** This project does use `bv_decide` for fixed-width goals, because 64-bit bit-trick identities (SWAR popcount, de Bruijn trailing zeros, carry formulas) are infeasible by `decide` or `omega`. The cost is the `Lean.ofReduceBool` axiom: the LRAT certificate is checked by a checker proven sound in Lean but executed through the compiler. The audit tool reports the trust tier (kernel-only versus `bv_decide`) for every theorem, and `native_decide` is banned by a source scan so that the axiom can only originate from `bv_decide`.

## 6. Uncertain or could not verify

From the julia-in-lean and Go-semantics report:

- No maintainer-stated "confirmed" bug count exists for julia-in-lean; 27 closed-as-completed issues and 45 merged PRs are proxies from the GitHub API, and `completed` is GitHub's default close reason. Filed counts differ by snapshot (75, 107, 108). No published fraction of intended-behaviour findings. Later Discourse pages not fetched.
- Whether `Lean.ofReduceBool` still exists after 4.35.0 removed `Lean.reduceBool`/`Lean.reduceNat`, and which axiom `bv_decide` and `native_decide` now emit; to be confirmed with `#print axioms` on the pinned toolchain.
- No published hard limits for `bv_decide` beyond the 10 s SAT timeout.
- K-Go repository and licence not found; Wolff/Paris-Saclay Isabelle semantics has no published output; Featherweight Go mechanisation absence rests on negative searches.
- Perennial `lean` branch licence not retrievable.
- Plausible's descent from `slim_check` inferred from Zulip discussions, not an explicit announcement.
- The Lean 4.12 blog post could not be fetched; release notes were used.

From the Gobra, Viper and Go-testing report:

- Gobra channel and `sync.WaitGroup` chapters: headings seen, bodies not read.
- Whether Gobra's stub directory is spec-only is inferred from the directory name; the DeepWiki description is unofficial.
- Which bugs VerifiedSCION found in SCION: README mentions fixes but lists none.
- Exact Go release containing the #63913 Insert fix (secondary source says Go 1.22).
- Merge state of Gobra PR #1015 after 2026-07-22.
- Whether commit 8dcb3171 has a linked issue or caused real-world miscompiles.
- golang_tv and ssarules last-commit dates and the golang_tv licence.
- Whether the golang-dev Alive proposal produced anything beyond golang_tv.
- The exact faulty rule in #15175.
- The stdlib issue list came from web search without live GitHub issue search and may be incomplete, especially for `bytes` and `sort`.
