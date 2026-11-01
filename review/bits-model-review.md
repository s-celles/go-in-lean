# Adversarial review: `GoInLean/Stdlib/Bits.lean` vs `$GOROOT/src/math/bits/bits.go` (go1.25.5)

Reviewer stance: try to falsify the claim that the Lean file is a faithful
transliteration of the portable Go code (assumption A4), and that the
`Properties/Bits.lean` oracles say what the Go doc comments promise.

Scope read in full: `GoInLean/Stdlib/Bits.lean`, `GoInLean/Stdlib/BitsTables.lean`
(header, `tab`, table sizes, generator `scripts/gen_bits_tables.py`),
`GoInLean/Semantics/Int.lean`, `GoInLean/Semantics/BitSpec.lean`,
`GoInLean/Properties/Bits.lean`, `docs/semantic-boundary.md`, `targets/properties.yaml`,
and `bits.go` / `bits_tables.go` / `bits_errors.go` of the pinned toolchain
(`/opt/homebrew/Cellar/go/1.25.5/libexec`, `go version go1.25.5 darwin/arm64`).

Nothing under `GoInLean/`, `targets/`, `docs/`, `scripts/` was modified. All test
programs live in the session scratch directory (`.../scratchpad/review/`): `gen/main.go`
(vector generator), `purebits/` (a copy of `bits.go` + `bits_tables.go` renamed to
package `purebits`, so the compiler does **not** intrinsify it and the *portable*
code path is exercised), `check.lean` (Lean-side evaluator), `probe.lean` /
`probe4.lean` (elaboration dumps, oracle sanity, fuel sensitivity), `loopcount/main.go`
(instrumented `Div64` loop counter).

## 1. Function-by-function fidelity table

Verdicts: **FAITHFUL** (same parse tree, widths, signedness, constants, panic order);
**DEVIATION-UNOBSERVABLE** (the Lean text differs from Go but no input on which Go
does not panic can distinguish them; argument given); **MISMATCH** (an input exists
on which the model and the Go portable code disagree). Evidence columns: *E* =
differential vectors (pure-Go copy vs Lean model, §2), *P* = kernel/`bv_decide`
proof already in `Properties/Bits.lean`, *A* = argument in this review.

| Function | Go lines | Verdict | Evidence / notes |
|---|---|---|---|
| `Len8` | 310-312 | FAITHFUL | `int(len8tab[x])` = `(tab len8tab x).zeroExtend 64`. E, P |
| `Len16` | 315-321 | FAITHFUL | both `if`s test the same original `x`; `1<<8` typed `uint16`; `n + int(tab)`. E, P |
| `Len32` | 324-334 | FAITHFUL | second test uses the shifted `x` (Lean rebinds `x` first). E, P |
| `Len64` | 337-351 | FAITHFUL | three-step cascade identical. E, P |
| `Len` | 302-307 | FAITHFUL (A1) | `UintSize == 32` branch dead under A1. E |
| `LeadingZeros{8,16,32,64}` | 28-37 | FAITHFUL | `N - LenN x` with Go `int` = `BitVec 64`. E, P |
| `LeadingZeros` | 25 | FAITHFUL (A1) | `UintSize - Len(x)` = `64 - Len64 x`. E |
| `TrailingZeros8` | 67-69 | FAITHFUL | table lookup. E, P |
| `TrailingZeros16` | 72-78 | FAITHFUL | Go parse: `(uint32(x&-x)*deBruijn32) >> 27` (`*`, `>>` same level, left-assoc). Lean: `((convU 32 (x &&& -x)) * deBruijn32) >>> (32-5)`; `#print` with `pp.explicit` confirms the shift count elaborates as `Nat` 27 and `-x` is `BitVec.neg` at width 16. Constant `0x077CB531` matches line 42. E, P |
| `TrailingZeros32` | 81-87 | FAITHFUL | same shape at 32 bits. E, P |
| `TrailingZeros64` | 90-106 | FAITHFUL | `0x03f79d71b4ca8b09` matches line 49; shift `64-6`. E, P |
| `TrailingZeros` | 59-64 | FAITHFUL (A1) | E |
| `OnesCount8` | 125-127 | FAITHFUL | E, P |
| `OnesCount16` | 130-132 | FAITHFUL | Go adds two `byte`s (max 16, no wrap) then `int()`; Lean adds `BitVec 8` then `zeroExtend`. E, P |
| `OnesCount32` | 135-137 | FAITHFUL | `x>>16&0xff` parses `(x>>16)&0xff`; four `byte`s sum ≤ 32. E, P |
| `OnesCount64` | 140-168 | FAITHFUL | `x>>1&(m0&m) + x&(m0&m)` = `((x>>1)&(m0&m)) + (x&(m0&m))` — Lean parenthesised exactly so (checked by `#print`). `m = 1<<64-1` modelled as `(1<<<64)-1 = all ones` in `BitVec 64`; `int(x) & (1<<7-1)` = `x &&& 127`. E, P |
| `OnesCount` | 117-122 | FAITHFUL (A1) | E |
| `RotateLeft{8,16,32,64}` | 187-221 | FAITHFUL | `uint(k) & (n-1)` is a bit-identity conversion then mask; `n-s` is a `uint` subtraction (never wraps, `s ≤ n-1`); `x>>(n-s)` with `s = 0` shifts by `n` → 0 in both (Lean `HShiftRight (BitVec 8) (BitVec 64)` uses `toNat`). Negative `k` tested (`k = 2^64-7`, `2^64-63`, `2^63`, …). E, P |
| `RotateLeft` | 176-181 | FAITHFUL (A1) | E |
| `Reverse8` | 234-236 | FAITHFUL | E, P |
| `Reverse16` | 239-241 | FAITHFUL | `uint16(rev8tab[x>>8]) \| uint16(rev8tab[x&0xff])<<8`; Lean `<<<` binds tighter than `\|\|\|`, and is parenthesised anyway. E, P |
| `Reverse32` | 244-250 | FAITHFUL | `m0&m` with `m = 1<<32-1` is the untyped constant `0x55555555`; Lean `convU 32 m0 &&& m` (function application binds tightest → `(convU 32 m0) &&& m`). `x&(m0&m)<<1` = `(x&(m0&m))<<1` (same level, left-assoc) — matches Lean. E, P |
| `Reverse64` | 253-259 | FAITHFUL | E, P |
| `Reverse` | 226-231 | FAITHFUL (A1) | E |
| `ReverseBytes16` | 276-278 | FAITHFUL | E, P |
| `ReverseBytes32` | 283-287 | FAITHFUL | `m3&m` → `0x00ff00ff` via `convU 32`. E, P |
| `ReverseBytes64` | 292-297 | FAITHFUL | E, P |
| `ReverseBytes` | 266-271 | FAITHFUL (A1) | E |
| `Add32` | 374-379 | FAITHFUL | widened to `uint64`, split with `>>32`. E, P |
| `Add64` | 386-393 | FAITHFUL | `((x & y) \| ((x \| y) &^ sum)) >> 63`; `&^` = `Go.andNot`. Includes the out-of-contract carries 2 and `MaxUint64`: Lean equals the *pure-Go* formula, and differs from the arm64 intrinsic exactly there (A4, see §2.2). E, P |
| `Add` | 360-367 | FAITHFUL (A1) | not in vectors; alias is definitional |
| `Sub32` | 416-424 | FAITHFUL | `((^x & y) \| (^(x ^ y) & diff)) >> 31`. E, P |
| `Sub64` | 431-436 | FAITHFUL | `>> 63`. Out-of-contract borrows: same remark as `Add64`. E, P |
| `Sub` | 402-409 | FAITHFUL (A1) | alias |
| `Mul32` | 459-463 | FAITHFUL | E, P |
| `Mul64` | 470-484 | FAITHFUL | `mulhiGeneric 32` is the schoolbook text with `mask32 = 2^32-1`; `t := x1*y0 + w0>>32` = `(x1*y0) + (w0>>32)`; `hi = x1*y1 + w2 + w1>>32` = `((x1*y1)+w2)+(w1>>32)`; `lo = x*y`. E (incl. 0xFFFF…×0xFFFF…, 2^63×2^63, de Bruijn constants); P only at `h = 4` |
| `Mul` | 445-452 | FAITHFUL (A1) | alias |
| `Div32` | 505-512 | FAITHFUL | panic order: `y != 0 && y <= hi` → `overflowError` first, then `z/uint64(y)` → `divideError` when `y == 0`. Lean tests `y ≠ 0 ∧ y ≤ hi` then `y = 0`. Tested with `y = 0` for `hi ∈ {0, x, …}`. E |
| `Div64` | 518-568 | DEVIATION-UNOBSERVABLE | Three textual deviations, each argued unobservable below (§1.1). Panic order (`y == 0` before `y <= hi`), fast path, normalisation, `un32 = hi<<s \| lo>>(64-s)`, both loops, `un21`, final `>> s` all match term-for-term. E (incl. `s = 0` cases, hard Knuth cases), P at `h = 4` |
| `Div` | 492-499 | FAITHFUL (A1) | alias |
| `Rem32` | 583-585 | FAITHFUL | single `%` on the 64-bit dividend; `divideError` iff `y == 0`; no overflow panic. E |
| `Rem64` | 590-599 | FAITHFUL | Go evaluates `hi%y` first (panics `divideError` when `y == 0`), then `Div64(hi%y, lo, y)`; Lean checks `y = 0` first, then `divGeneric (hi % y) lo y`. Overflow is impossible since `hi%y < y`. E |
| `Rem` | 573-578 | FAITHFUL (A1) | alias |

### 1.1 The deliberate deviations in `divGeneric` (Go `Div64`)

1. **`s := uint(LeadingZeros64(y))` replaced by `BitSpec.clzW y`.** Unobservable at
   `h = 32`: `Properties.LeadingZeros64_eq_clzW` (via `LeadingZeros64_spec` and
   `clzW_eq_clz64`, both `bv_decide`) proves pointwise equality on all of `uint64`.
   At other `h`, `divGeneric h` is not a model of any Go function, so no claim is
   affected. I also evaluated `clzW` on `0x1`, `0` at width 8 (7, 8) — sane.
2. **`for` loops as `divCorrect … 8 …` (fuel 8).** Unobservable: the Go loop body
   executes at most twice. Argument: on entry `rhat = un32 − q1·yn1 = un32 mod yn1 < yn1 < 2^32`
   (`yn1 ≥ 2^31` because `y` is normalised); each iteration adds `yn1 ≥ 2^31` to
   `rhat` without 64-bit wrap (`rhat < 2^33`), so after the second iteration
   `rhat ≥ 2^32` and the `break` fires. Same for the second loop with `un21 mod yn1`.
   Fuel 8 ≥ 3 therefore reproduces Go exactly; the fuel-exhausted branch (`| 0, q, _ => q`)
   is unreachable. Experimental confirmation: instrumented Go copy, 40,000,000
   random/structured non-panicking triples: histogram of iteration counts
   `{0: 56,370,008; 1: 21,713,726; 2: 1,916,266}`, maximum 2 in both loops; and
   exhaustive comparison of `divGeneric` with fuel 2 / 8 / 100 at `h = 1, 2, 3`
   and `h = 4` (all 2^{6h} triples): 0 fuel-sensitive triples, 0 disagreements with exact
   `Nat` division (§2.3).
3. **Bare `BitVec` `/`, `%` instead of `Go.divU/remU`.** `lo / y`, `lo % y` are
   guarded by `y ≠ 0`; `un32 / yn1`, `un21 / yn1` have `yn1 ≥ 2^(h-1) ≥ 1` after
   normalisation. Lean's `x / 0 = 0` convention is never reached. Unobservable.
4. **`tab` returns 0 out of range (Go would panic).** Every index is provably in
   range: `Len*` shift until `x < 256`; the de Bruijn indices are `>> 27` / `>> 58`
   of a 32-/64-bit word (`< 32` / `< 64`); `pop8tab`/`rev8tab` indices are a byte
   (`>> 8` of a `uint16`, or `& 0xff`). The properties file discharges each of these
   (`tab_len8_of_lt`, `tab_deBruijn32_of_lt`, `tab_deBruijn64_of_lt`, `tab_lt`). Unobservable.

### 1.2 Items checked and found correct (so the "nothing found" is not for lack of looking)

* Operator precedence (A6): every binary expression of `bits.go` was re-parsed by
  hand with Go's two levels and compared to the Lean parenthesisation; `#print`
  with `pp.explicit` of `TrailingZeros16`, `RotateLeft8`, `OnesCount64`, `Len16`
  confirms the elaborated trees (shift counts are `Nat` where literal, `BitVec 64`
  where the Go code uses a `uint` variable; `-x` is two's-complement negation).
* Widths of conversions: `uint32(x&-x)` (16→32 zero-extend), `uint64(x)` in
  `Add32`/`Mul32`/`Div32`/`Rem32`, `uint32(tmp>>32)`, `int(byte)` → all `convU`/`zeroExtend`.
* Signedness: no signed operation in `bits.go`; the only `int` operands are `k`
  in `RotateLeft*` (converted `uint(k)` → bit identity) and the `int` results
  (zero-extended bytes, or small differences that never go negative).
* Constants: `deBruijn32/64`, `m0…m4`, the `1<<7-1` mask, `two32`/`mask32` all
  re-read against the Go source; table contents are generated byte-for-byte from
  `bits_tables.go` (sha256 recorded in the generated header matches the pinned file).
* Panic order and conditions for `Div32`, `Div64`, `Rem32`, `Rem64` (above).
* `UintSize == 32` branches are dead under A1 and modelled as aliases.
* Line references in the Lean section comments are approximate (e.g.
  "TrailingZeros 42-111" is really 42-106; "OnesCount 110-160" is 110-168;
  "Div 490-570" is 492-568). Cosmetic only.

## 2. Differential testing performed

### 2.1 Pure-Go vs Lean model

`gen/main.go` evaluates the **non-intrinsified copy** (`purebits`) *and* the real
`math/bits` on the same inputs, prints the pure-Go results, and flags any
pure-vs-std disagreement on stderr. `check.lean` re-evaluates every line with the
Lean model via `lake env lean --run` (compiled-evaluator semantics, Lean
`v4.35.0` toolchain of the project).

Inputs: 690 64-bit values (0, 1, 2, 3, powers of two, `2^i-1`, `~(2^i)`, `~(2^i-1)` for
i < 64, the mask constants, both de Bruijn constants, 300 PCG-random words, 100
random words right-shifted by a random amount) for the unary functions (truncated
to 8/16/32 bits as needed); 46 rotation counts including 0, 7, 8, 9, 63, 64, 65,
`2^63`, `2^63-1`, `MaxUint64`, `MaxUint64-63`, `MaxUint64-64` and random; all
ordered pairs of the first 440 values for `Add/Sub` (carry/borrow ∈ {0, 1, 2, MaxUint}),
`Mul`, `Div`, `Rem`; `Div64/Rem64` with `hi ∈ {0, x, y, y-1, y>>1, x % (y|1), (y-1)&x, x%y}`;
plus 780 hand-picked Knuth hard cases (divisors `0x8000000000000001`,
`0x80000000ffffffff`, `0xffffffff00000000`, `0x100000001`, `0x1ffffffff`,
`0x7fffffff00000001`, `0xfffffffe00000001`, …; `hi ∈ {y-1, y>>1, (y>>1)+1, 1, y-2, y/3}`;
`lo ∈ {0, 1, MaxUint64, 0xffffffff00000000, 0x00000000ffffffff, 2^63, 2^63-1, y-1, y, ~y}`),
which include `s = 0` (`y ≥ 2^63`) and both-correction-loop cases.

Totals: **9,051,590 vectors** generated. Sampled run (every 13th binary/ternary
vector, all unary vectors): **831,941 vectors checked, 0 mismatches**
(`Div64` 119,132; `Rem64` 119,071; `Div32` 89,353; `Rem32` 89,354; `Add64` 59,571;
`Sub64` 59,570; `Add32`/`Sub32` ≈ 59.6k each; `Mul64` 14,892; `Mul32` 14,893;
`RotateLeft*` 31,740 each; 690 each for the other unary functions and the `uint` aliases).
Full run (all 9,051,590 vectors, `lean_check_full.log`, 2 min): **9,051,590 checked, 0 mismatches, 0 unknown functions**.

Representative individual vectors (Go pure = Lean in every case):

| Call | Go (pure) | Lean |
|---|---|---|
| `TrailingZeros16(0x8000)` | 15 | 15 |
| `TrailingZeros64(0x8000000000000000)` | 63 | 63 |
| `OnesCount64(0xffffffffffffffff)` | 64 | 64 |
| `RotateLeft8(0x81, -1)` (k = MaxUint64) | 0xC0 = 192 | 192 |
| `RotateLeft64(x, 64)` | x | x |
| `Reverse32(0x077CB531)` | 0x8CAD3EE0 | same |
| `Add64(MaxUint64, MaxUint64, 2)` | (0, 1) pure / (MaxUint64, 1) intrinsic | (0, 1) |
| `Sub64(0, 0, 2)` | (MaxUint64-1, 1) pure / (MaxUint64, 1) intrinsic | (MaxUint64-1, 1) |
| `Mul64(MaxUint64, MaxUint64)` | (MaxUint64-1, 1) | same |
| `Div64(1, 0, 0x8000000000000001)` (`s = 0`) | (1, 0x7fffffffffffffff) | same |
| `Div64(2^63, MaxUint64, 2^63+1)` (`s = 0`, `hi = y-1`) | (MaxUint64, 2^63) | same |
| `Div64(1, 0, 1)` | panic overflowError | `.error .overflowError` |
| `Div64(0, 0, 0)`, `Div64(x, x, 0)` (y ≤ hi too) | panic divideError (checked before overflow) | `.error .divideError` |
| `Div32(0, 0, 0)`, `Div32(x, x, 0)` | panic divideError | `.error .divideError` |
| `Rem64(MaxUint64, MaxUint64, 0x100000001)` (hi ≥ y: Div64 would overflow) | 0, no panic | `.ok 0` |
| `Rem64(0, 0, 0)` | panic divideError | `.error .divideError` |

(The exact values for every row are in `scratchpad/review/vectors.txt`; the Lean
check output is `lean_check.log` / `lean_check_full.log`.)

### 2.2 Intrinsic vs portable (A4 cross-check, not a model defect)

Over the 9.05M vectors the only pure-vs-`math/bits` disagreements were the
**774,400** `Add64`/`Sub64` vectors with carry/borrow ∈ {2, MaxUint64}
(out of contract, golang/go#54255, already recorded as `BITS-ADD-64-NOPRE` and
`TestAdd64CarryTwoIsOutOfContract`). `Add32`/`Sub32` agree even out of contract
(the pure code widens to 64 bits). All in-contract calls of every function agree
between the arm64 intrinsics and the portable code, so the model also agrees with
the compiled standard library on every in-contract input tested.

### 2.3 Fuel and exactness of `divGeneric` at small widths

`probe.lean`: a copy of `divGeneric` with the fuel as a parameter, compared with
fuel 2 / 8 / 100 and with exact `Nat` arithmetic over **all** triples
`(hi, lo, y)` at width 2, 4 and 6 bits (`h = 1, 2, 3`): 24 / 1,920 / 129,024
non-panicking triples, **0 wrong, 0 fuel-sensitive**; every panicking triple
panics in the model too. Width 8 (`h = 4`, all 16,777,216 triples, 4 min): **8,355,840 non-panicking triples, 0 wrong, 0 fuel-sensitive** — an independent executable confirmation of `divGeneric_4_spec` and of the yaml note that fuel 2 suffices.

## 3. Specification (oracle) weaknesses in `Properties/Bits.lean`

None of these is a soundness problem; they are places where the stated theorems are
weaker than the Go doc comment, trivially true, or restate the implementation.

1. **`Mul64` at the real width is unproved and the manifest's `lean_theorem`
   entries are tautologies.** `Mul64_lo` and `Mul64_hi_def` are `rfl`; the
   128-bit product property is proved only for `mulhiGeneric 4` (8-bit words).
   `targets/properties.yaml` `BITS-MUL-64` lists them under `trust: kernel`,
   `status: inconclusive` — honest, but a reader of the theorem list alone could
   mistake them for evidence. A `Nat`-level proof (`toNat` arithmetic, no SAT) of
   `mulhiGeneric h` for all `h` is feasible and would close this.
2. **`Div64` at the real width is unproved**; `BITS-DIV-64` lists
   `LeadingZeros64_eq_clzW` as its `lean_theorem`, which is only the oracle link,
   not the property. Status `inconclusive` is accurate. `divGeneric_ok` (∃ r, ok r)
   is deliberately weak — it says nothing about the value.
3. **No theorem at all for `Div32`, `Rem32`, `Rem64`/`remGeneric`.** In
   particular the doc promise "unlike Div64, it doesn't panic on a quotient
   overflow" is provable for every `h` (`hi % y < y`) with the existing
   `divGeneric_ok`, but is not stated. `Div32`/`Rem32` correctness is a 64-bit
   division — hard for `bv_decide`, but could be stated via `divSpec 16`.
4. **`Add64_carryOut_le_one` / `Sub64_borrowOut_le_one` are structurally
   trivial**: any `(… ) >>> 63` of a 64-bit word is ≤ 1, independent of the
   formula. They are true for carry = 2 as well, i.e. they do not detect the
   out-of-contract behaviour. The real content is in `Add64_spec` / `Sub64_spec`
   (which do carry the `carry ∈ {0,1}` hypothesis and are the right statement).
5. **`RotateLeft*_spec` use core `BitVec.rotateLeft` as the oracle**, not a
   `BitSpec` definition. Acceptable (it is independent of the Go text), but it is
   the one spec whose meaning depends on a library definition rather than an
   unrolled fold; the `k.toNat % N` phrasing silently relies on two's-complement
   for negative `k` (noted in the yaml history). `RotateLeft64_neg` covers the
   doc sentence about negative `k`; there is no `_neg` theorem for 8/16/32.
6. **Doc clauses not modelled**: "execution time does not depend on the inputs"
   (`RotateLeft*`, `ReverseBytes*`, `Add*`, `Sub*`, `Mul*`) — not expressible in
   this model; worth saying so explicitly in the manifest rather than omitting.
7. **`uint` aliases** (`Len`, `LeadingZeros`, `TrailingZeros`, `OnesCount`,
   `RotateLeft`, `Reverse`, `ReverseBytes`, `Add`, `Sub`, `Mul`, `Div`, `Rem`)
   have no theorems and no vectors in the repo's `gen_vectors.go` (they are
   definitional aliases, so this is harmless; my vectors cover the unary ones).
8. **Oracles checked and found faithful to the doc comments**: `len` (1 + index of
   highest set bit, 0 for 0), `clz`/`clzW` (`w` for 0), `ctz` (`foldr` makes the
   *lowest* set bit win; `w` for 0 — checked `ctz 0x80 = 7`, `ctz 6 = 1`, `ctz 0 = 8`),
   `popcount`, `reverse` (bit `i` ← bit `w-1-i`), `reverseBytes{16,32,64}` (`++`
   puts the first argument high: `reverseBytes32 0x11223344 = 0x44332211`),
   `divSpec` (4h-bit dividend, exact; `setWidth` is lossless under `hi < y`),
   `mulhiSpec`, the 128-bit `Add64`/`Sub64` identities (sound: `carryOut ≤ 1`
   makes `|||` a `+`; the `Sub64` identity in `Z/2^128` forces the integer identity
   because all terms are `< 2^66`). The `BITS-ADD-64-NOPRE` negative control is
   genuinely refuted by `decide` at `x = y = MaxUint64, carry = 2`.

## 4. Verdict

**No MISMATCH found.** Every function of `bits.go` is either a term-for-term
transliteration (FAITHFUL) or differs only in ways proved/argued to be
unobservable on non-panicking inputs (`Div64`: `clzW` oracle, fuel-8 loops, bare
`/`; all tables: `tab` out-of-range default). The model agrees with the pure-Go
code on all 9,051,590 differential vectors run, including deliberately adversarial `Div64` inputs, `s = 0`
normalisation, both correction loops firing, negative rotation counts, and
out-of-contract carries (where it correctly reproduces the *portable* formula
rather than the intrinsic, as A4 states).

Confidence: **high (≈ 0.95)** that `GoInLean/Stdlib/Bits.lean` is a faithful model
of the portable go1.25.5 `math/bits` under A1–A6. Residual risk is concentrated in
(i) `Mul64`/`Div64` at width 64 having only testing and small-width proofs, not
proofs at the real width, and (ii) the specification gaps listed in §3 (notably no
statement at all for `Rem64`'s "never overflows" promise and for `Div32`/`Rem32`).
