# BITS-ADD-64-NOPRE: `bits.Add64` carry formula with an out-of-contract carry input

**Classification:** `known_issue` (previously `counterexample_in_model`). **Not a Go defect.**

**Human review status:** reviewed in-session by the modelling agent only;
recorded as a negative control that exercises the full pipeline. No upstream
action.

## Expected behaviour (property as first stated)

For all `x, y, carry : uint64`, `carryOut·2^64 + sum = x + y + carry` as a
128-bit integer, where `(sum, carryOut) = Add64(x, y, carry)`.

## Actual behaviour

The pure-Go implementation (`src/math/bits/bits.go:386-394`, go1.25.5)
computes `carryOut = ((x & y) | ((x | y) &^ sum)) >> 63`, which is a single
bit. For `carry = 2` the true carry can be 2, so the property is false.

* Lean counterexample (bv_decide, then kernel-checked negation
  `Go.Bits.Properties.Add64_nopre_refuted`): `x = y = 0xFFFFFFFFFFFFFFFF`,
  `carry = 2`. Model result `(sum, carryOut) = (0, 1)`; true 128-bit sum `2^65`.
* Go reproduction (`go/tests/bits_test.go`, `TestAdd64CarryTwoIsOutOfContract`),
  go1.25.5 darwin/arm64:
  * pure-Go formula: `(0x0, 0x1)` (matches the Lean model exactly);
  * `bits.Add64` as compiled (arm64 intrinsic): `(0xffffffffffffffff, 0x1)`.
  The two Go answers differ from each other and from the mathematical sum.

## Behavioural contract

The doc comment says: "The carry input must be 0 or 1; otherwise the
behavior is undefined." The property violated the precondition. With the
precondition, the identity is proved (`Go.Bits.Properties.Add64_spec`,
BITS-ADD-64).

## Known-issue search

golang/go#54255 "math/bits: different results from pure-Go copy of Add64"
reports exactly this intrinsic-vs-pure-Go divergence for `carry = 2` and was
closed as working as intended (https://github.com/golang/go/issues/54255).

## Reproduction commands

```sh
lake build                                     # includes Add64_nopre_refuted
cd go && go test ./tests -run TestAdd64CarryTwoIsOutOfContract -v
```

## Assumptions and limitations

Assumption A4 (`docs/semantic-boundary.md`): the Lean model is the portable
code path; the compiled function may be an intrinsic. This finding is the
concrete demonstration of why `proved_in_model` does not mean "verified Go
binary".

## Confidence

High that the behaviour is as described; high that it is not a bug
(documented precondition + maintainers' ruling in #54255).
