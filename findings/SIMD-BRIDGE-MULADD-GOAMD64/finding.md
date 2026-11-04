# SIMD-BRIDGE-MULADD-GOAMD64: emulated MulAdd double-rounds on amd64 at GOAMD64=v1/v2, and the generic emulation is unfused on 32-bit targets

Found 2026-11-04 by the J3 cross-arch float campaign of the Lean SIMD spec
oracle (`scripts/simd_oracle.py --float`, cross-arch flow via `GOEXEC` /
`GO_ONLY` / `GO_FROM_FILE`, 7 architectures x 50 seeds x 2 configurations on
GEEKR9 under qemu). Filed as review feedback for golang/go#80355 / CL 799281
(the root cause is already tracked upstream; both instances below escape the
CL's current patch).

## Status

- Root cause: golang/go#80355 (open), fix in review as CL 799281 (NEW,
  touches only `src/simd/simd_emulated.go`).
- Review comment published on CL 799281 (2026-11-04, patchset message +
  inline comment at src/simd/simd_emulated.go:2661) - the draft in
  `cl799281-comment.md` is the posted text.
- Complete fix mailed as [CL 858921](https://go-review.googlesource.com/c/go/+/858921)
  (branch fix-80355-bridge, commit 8b21d1bde4, rebased on master 672197524b,
  regenerated bridge, `go test ./src/simd/` and the differential campaign
  re-validated on the rebased tree).
- This finding: two gaps of CL 799281, with reproduction and a validated
  complete fix (local branch `fix-80355-bridge`, commit 3b6ad8f97d on top of
  go master 7ad446c0ec).

## What the campaign measured

`Float32s/Float64s MulAdd` versus the fused single-rounding semantics the
package documents ("a fused multiply-add ... with a single rounding ...
except on wasm"), canary `MulAdd((1+2^-w), (1+2^-w), -(1+2^(1-w)))`:

| Configuration | Result | Verdict |
|---|---|---|
| amd64 native (GODEBUG=simd=128) | fused | conform |
| arm64 native (qemu-aarch64) | fused | conform |
| riscv64 / ppc64le / s390x emulated (generic `simd_emulated.go`) | fused | conform - the gc compiler contracts `x*y+z` into a hardware FMA on these backends (Go permits it) |
| **386 / arm / mipsle emulated (generic `simd_emulated.go`)** | **double-rounded** | **violates the documented semantics - golang/go#80355; identical 28/50 divergent seeds across all three, both GODEBUG configurations** |
| **amd64 GODEBUG=simd=0, GOAMD64=v1/v2 (the midway bridge `internal/bridge/simd_emulated.go`)** | **double-rounded** | **violates the documented semantics; NOT in #80355's stated scope ("architectures other than amd64, arm64, and wasm")** |
| amd64 GODEBUG=simd=0, GOAMD64=v3 | fused | conform by accident (the gc compiler contracts at GOAMD64>=v3) |
| wasm | double-rounded | documented exception, conform |

The amd64 line is the sharpest repro: the same binary on the same machine
computes different `MulAdd` results depending on `GOAMD64`:

```
$ GOAMD64=v1 GODEBUG=simd=0 ./canary   # 0x0000000000000000 (double-rounded)
$ GOAMD64=v2 GODEBUG=simd=0 ./canary   # 0x0000000000000000 (double-rounded)
$ GOAMD64=v3 GODEBUG=simd=0 ./canary   # 0x3970000000000000 (fused)
$ GODEBUG=simd=128 ./canary            # 0x3970000000000000 (fused)
```

with the float64 canary `MulAdd((1+2^-52), (1+2^-52), -(1+2^-51))` whose
fused result is 2^-104 and whose double-rounded result is 0 (and the float32
analog: 2^-46 = 0x28800000 vs 0).

## Why the bridge instance escapes CL 799281

`internal/bridge/simd_emulated.go` is generated verbatim from
`src/simd/simd_emulated.go` by `generateBridgeEmulated()` in
`src/simd/archsimd/_gen/midway/intersect_simd_ops.go` (it only flips the
build tag and the package name). The CL fixes the source file but does not
regenerate the bridge, so after merge the amd64/arm64/wasm emulation paths
(`GODEBUG=simd=0` and missing-CPU-feature fallbacks) keep the double-rounding
`MulAdd` at GOAMD64=v1/v2. Regeneration is part of the complete fix
(`go run -C $GOROOT/src/simd/archsimd/_gen/midway -goroot $GOROOT -w`).

## The Float32 form in CL 799281 double-rounds

The CL computes the float32 case as
`float32(math.FMA(float64(x), float64(y), float64(z)))`. The float64 FMA is
correctly rounded to float64, but converting it to float32 rounds a second
time; when the exact value lies within half a float64 ulp of a float32
midpoint, the conversion can round in the wrong direction. The reference
implementation the conformance tests use - `fma32` in
`src/simd/internal/spec/mathlib.go` - already documents and fixes exactly
this with round-to-odd (Boldo & Melquiond, "Emulation of a FMA and
correctly rounded sums"). The CL's 800k-triple verification compared
against the same naive form, so it could not see the difference.

Counterexamples (found by differential search over the double-rounding
region - product around 1, addend at 2^-32..2^-27 - each verified against
200-bit exact arithmetic and independently against exact fraction rounding):

```
x=3fb8242d y=3fe54e4a z=b09580ff: exact=4024f0ad naive=4024f0ac
x=3ffdc557 y=3fff878d z=2fdc2a01: exact=407d4df1 naive=407d4df0
x=3fda2144 y=3fef38bf z=b0d8ddfe: exact=404bd569 naive=404bd568
x=3f910eab y=3f829e58 z=b014c802: exact=3f940657 naive=3f940658
```

(one ulp off in every case; the round-to-odd form matches the exact result).

## Validated fix (local branch fix-80355-branch, commit 3b6ad8f97d)

- Float64s: `math.FMA` (correctly rounded unconditionally).
- Float32s: the round-to-odd `fma32` from `internal/spec`, inlined with the
  Boldo & Melquiond citation.
- `internal/bridge/simd_emulated.go` regenerated.

Validation:

- Canary: amd64 GOAMD64=v1/v2/v3 + GODEBUG=simd=0 all fused now
  (0x3970000000000000 / 0x28800000); hardware path unchanged.
- The 100-seed emulated float campaign that diverged on 53/100 seeds
  against the Lean spec oracle now runs **0/100 divergent, 0 build
  failures** (1000 chains), mutually validating the fix and the oracle.
- `go test ./src/simd/` passes.

## Notes

- The 32-bit generic-emulation line (386/arm/mipsle) is #80355 itself;
  the CL fixes it, provided the two gaps above are closed.
- wasm's unfused MulAdd is the documented exception; not a finding.
- The amd64 Min/Max NaN and +-0 deviations seen in the same campaign are
  documented architecture-dependent behaviour (the stubs table), not
  findings.

Assisted by AI.
