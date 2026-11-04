# cmd/compile: GOEXPERIMENT=simd amd64 fails to build IfElse of a constant shift ("invalid instruction" VPSLLQ Z0, K1, Z1)

<!-- Draft golang/go issue — no fix included (Gerrit CL follows). "Assisted by AI." closes the body. -->

### Go version

```
go version devel go1.28-740d909bb5 linux/amd64
```
(also present on go1.28-devel at 2b74366d)

### Does this issue reproduce with the last release?

N/A — GOEXPERIMENT=simd.

### What operating system and processor architecture are you using?

linux/amd64 (any amd64; the failing variant is generated regardless of the host CPU).

### What did you do?

Compile the following with `GOEXPERIMENT=simd go build`:

```go
package main

import "simd"

//go:noinline
func f(x, y simd.Uint64s, m simd.Mask64s) simd.Uint64s {
	return x.ShiftAllLeft(2).IfElse(m, y)
}

func main() {}
```

### What did you expect to see?

A successful build. `x.ShiftAllLeft(2).IfElse(m, y)` selects the shifted lanes
where the mask is true and `y` elsewhere; all variants (128/256/512-bit) should
compile.

### What did you see instead?

```
main.f@simd512: invalid instruction: 00007 (/tmp/smin/main.go:10)	VPSLLQ	Z0, K1, Z1
```

The 512-bit variant fails to assemble: the instruction the compiler emits has no
immediate operand, and the assembler's masked immediate-shift form requires one.

Scope (checked empirically): all 16/32/64-bit integer vector types with
`ShiftAllLeft`/`ShiftAllRight`, any constant shift count, only the `@simd512`
variant; the same shapes compile at 128 and 256 bits. Affected instructions:
VPSLLW/D/Q, VPSRAW/D/Q, VPSRLW/D/Q.

`GOEXPERIMENT=simd go vet`/`go build` fail at compile time; no binary is produced,
so this is a build failure, not a miscompilation.

Provenance: found by a cross-configuration differential fuzzer for the simd
package (generated chains over the portable API compared across GODEBUG vector
sizes and GOARCHes); the failure surfaced while building one of its programs.

Assisted by AI.
