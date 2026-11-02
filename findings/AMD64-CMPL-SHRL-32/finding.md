# AMD64-CMPL-SHRL-32: a flag-folding rule that is wrong for a count its own condition admits

**Classification:** `counterexample_in_model`, **latent / unreachable**: no Go program
compiled by go1.25.5 can trigger it. Severity today: none. Potentially novel.
**Human review status:** pending. Recommendation: at most a one-line robustness fix
(`c <= 31`), low priority; not a bug report.

## The rule

`src/cmd/compile/internal/ssa/_gen/AMD64.rules:1197` (go1.25.5):

```
(CMPLconst (SHRLconst _ [c]) [n]) && 0 <= n && 0 < c && c <= 32 && (1<<uint64(32-c)) <= uint64(n) => (FlagLT_ULT)
```

It folds "the 32-bit value `x >> c` is unsigned-below `n`" to a constant flag. On x86 a
32-bit `SHR` masks its count to 5 bits, so `SHRLconst [32]` is a shift by 0: the value is
`x`, which is not below `n` in general. With `c = 32` the condition reduces to `1 <= n`, so
e.g. `n = 1`, `x = 5` makes the rule claim `5 < 1`.

## Why it is unreachable

The only producer of `SHRLconst` in go1.25.5 is
`AMD64.rules:791 (SHRL x (MOV(Q|L)const [c])) => (SHRLconst [int8(c&31)] x)`, which emits
counts in `[0, 31]`; no Go code in `ssagen` or `amd64` builds the op directly (grep of
`OpAMD64SHRLconst`). The symmetric rule for `SHRQconst` (`c <= 64`) has the same property
with its producer emitting `c&63`.

## Evidence

* `GoInLean/Compiler/AMD64Latent.lean`: `cmpl_shrl_sound` (the rule is sound for every
  count in `1..31`), `cmpl_shrl_c32_refuted` (kernel-checked refutation at `c = 32`),
  `producer_range`.
* Found by the independent reviewer agent (`review/compiler-shift-review.md`, item 5),
  then restated and re-checked here.
* No Go reproducer is possible without modifying the compiler; this is stated, not hidden.

## Known-issue search

Not performed beyond reading the rule history; the rule is old and its `c <= 32` bound looks
intentional for the "shift out everything" intuition (true on most ISAs, not for x86 masks).
