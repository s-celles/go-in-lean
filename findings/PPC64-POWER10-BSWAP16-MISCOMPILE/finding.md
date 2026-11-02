# PPC64-POWER10-BSWAP16-MISCOMPILE: `ReverseBytes16` mistyped as 64-bit uint miscompiles on Power10

**Classification:** `go_discrepancy_reproduced`. **Compiler miscompilation (wrong code).**
**Impact: silent wrong results** from safe Go on `GOPPC64=power10`: the prove pass derives a false
sign fact about `^int16(bits.ReverseBytes16(k))` and folds a comparison / branch to the wrong
value. **No out-of-bounds access was demonstrated** (see below): the index and bounds-check paths
tested remain correctly checked.
**Same class as the public findings** #82772-#82777 (an SSA value typed wider than the quantity it
computes). It is kept in the private repo for now only on the maintainer's instruction; on the
evidence it is an ordinary miscompilation and could be handled publicly like the others.
**Affected:** `GOARCH=ppc64le`/`ppc64` with `GOPPC64=power10`. go1.27.x and master (confirmed
a0c8470e, 2026-11-02). go1.26 and earlier, and `GOPPC64=power9`, are correct. A go1.27 regression.
**Disclosure status:** reported publicly as [golang/go#82782](https://github.com/golang/go/issues/82782) after review (2026-11-02), handled like the sibling miscompilations #82772-#82777.

## Summary

The Power10 `ReverseBytes16` intrinsic (`ssagen/intrinsics.go`, `cfg.goppc64 >= 10`, "use BRH")
builds `OpBswap16` with result type `types.Types[types.TUINT]` (unsigned, 64-bit); the loong64 and
riscv64 intrinsics use `TUINT16`. The value holds a 16-bit byte reversal but is typed as a 64-bit
unsigned, so prove/knownbits get a false fact (effectively "bit 15 is 0", i.e. `int16(v) >= 0`
always). In go1.27 prove uses it to fold a sign comparison / branch to the wrong result.

## Confirmed symptom (wrong value)

```go
//go:noinline
func f(k uint16, y, z int16) int16 {
	r := ^int16(bits.ReverseBytes16(k))
	if y <= z {
		r = 7
	}
	return r
}
// GOPPC64=power10: f(0x0400, 5, 1) == 7. Spec: 5<=1 is false, so r stays ^0x0004 == -5.
// power9, amd64, arm64, go1.26: -5.
```

## Out-of-bounds: tested and NOT observed

A natural worry is that the same false fact removes a bounds check (an out-of-bounds read).
Three canary experiments say it does not, on the patterns tested:

* `if ^int16(ReverseBytes16(k)) < 0 { return s[i] }` with `i` out of range: `main.oob` compiles to
  `MOVD $0,R3; RET` (returns 0, no load). prove folded the guard to *false* and deleted the whole
  `s[i]` branch, so there is no access. A sentinel past the slice is never returned.
* Indexing `s[int(ReverseBytes16(k))]` on a length-32768 slice with the value's bit 15 set: the
  disassembly keeps the bounds check (`RLWINM` masks to 16 bits, `CMPU`+`BLE` to
  `runtime.panicBounds`); it panics correctly.

So the demonstrated effect is a wrong value / wrong branch, not a memory-safety violation. A real
out-of-bounds would need a pattern where the false fact removes a live index check; none was found.
(Method note: `go tool objdump -s 'main\.<fn>$' ./bin` plus a sentinel in valid backing memory is
the way to tell an eliminated check with a surviving load from a deleted branch.)

## Versions (2026-11-02, qemu-ppc64le 11.1.2)

| Toolchain | power10 | power9 |
|---|---|---|
| go1.21.13 .. go1.26.10 | correct | correct |
| go1.27.3, master a0c8470e | **wrong (7, want -5)** | correct |
| master + `fix.patch` | correct | correct |

With `fix.patch` (type the Power10 `OpBswap16` as `TUINT16`), the symptom is gone;
`go test -short cmd/compile/internal/ssa cmd/compile/internal/test` and
`go test -count=1 cmd/internal/testdir -run Test/codegen` pass.

## Lean model (`property.lean`, kernel-only)

Models the type-level root cause: `^int16(bswap16 x)` takes both signs, so no "bit 15 = 0" /
non-negativity invariant holds; the fix (true 16-bit type) leaves the comparison genuinely
two-sided.

## How it was found

`go-in-lean` public `metamorphic_fuzz.py --bits`, `GOPPC64=power10` variant.

## Disclosure

Originally treated as a potential bounds-check-elimination / OOB issue and kept private. The canary
experiments above disprove an out-of-bounds access on the patterns tested, leaving a wrong-code
miscompilation of the same class as the already-public #82772-#82777. Recommendation: unless a real
OOB pattern is found, handle it publicly like the others (a golang/go issue plus a Gerrit CL). Kept
private pending the maintainer's decision.
