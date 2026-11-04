# Draft Gerrit review comment for CL 799281

Two gaps, with repro; both found by differential fuzzing against an
executable Lean model of the package's documented semantics (the fused
side), across architectures under qemu.

## 1. The midway bridge needs regeneration too

internal/bridge/simd_emulated.go is generated verbatim from
src/simd/simd_emulated.go (generateBridgeEmulated in
src/simd/archsimd/_gen/midway/intersect_simd_ops.go flips only the build
tag and package name). The change as uploaded fixes the generic emulation
used on architectures other than amd64/arm64/wasm, but the bridge copy
keeps the plain x*y+z, so the emulation paths of amd64/arm64/wasm
(GODEBUG=simd=0, and missing-CPU-feature fallbacks) still double-round.

On amd64 this is observable as a GOAMD64-dependent result from the same
binary (Float64s canary MulAdd((1+2^-52), (1+2^-52), -(1+2^-51)), fused
result 2^-104 = 0x3970000000000000, double-rounded 0):

    GOAMD64=v1 GODEBUG=simd=0 -> 0   (v2 same; v1 is the default)
    GOAMD64=v3 GODEBUG=simd=0 -> 0x3970000000000000
    GODEBUG=simd=128           -> 0x3970000000000000

because the compiler only contracts x*y+z into FMA at GOAMD64>=v3. The
same holds for Float32s (0x28800000 vs 0). Rerunning the midway generator
(`go run -C $GOROOT/src/simd/archsimd/_gen/midway -goroot $GOROOT -w`)
propagates the fix to the bridge.

## 2. The float32 form double-rounds

float32(math.FMA(float64(x), float64(y), float64(z))) rounds twice: the
float64 FMA result is correctly rounded to float64, and converting to
float32 rounds again. When the exact value lies within half a float64 ulp
of a float32 midpoint the conversion can round the wrong way. fma32 in
src/simd/internal/spec/mathlib.go already handles exactly this with
round-to-odd (Boldo & Melquiond); the 800k-triple check in the
description compared against the same naive form, so it could not see it.

Counterexamples (one ulp off; verified against exact 200-bit arithmetic
and independently by exact fraction rounding; the round-to-odd form
matches the exact result on all four):

    x=3fb8242d y=3fe54e4a z=b09580ff: exact=4024f0ad naive=4024f0ac
    x=3ffdc557 y=3fff878d z=2fdc2a01: exact=407d4df1 naive=407d4df0
    x=3fda2144 y=3fef38bf z=b0d8ddfe: exact=404bd569 naive=404bd568
    x=3f910eab y=3f829e58 z=b014c802: exact=3f940657 naive=3f940658

Suggestion: use the internal/spec fma32 logic (Fast2Sum error term +
round-to-odd nudge) for the float32 case, and include the regenerated
bridge in the change.

With both gaps closed, a 1000-chain differential campaign against the
fused reference (amd64, GODEBUG=simd=0, both float widths, MulAdd-heavy
chains) goes from 53% divergent seeds to zero; GODEBUG=simd=0 then agrees
with the hardware at every GOAMD64 level. Happy to share the campaign
harness if useful.
