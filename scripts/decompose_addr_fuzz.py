#!/usr/bin/env python3
"""Generate deterministic programs for differential testing of Go's decomposeAddr pass.

The generated program deliberately takes addresses of small local aggregates, mutates fields
through those addresses across control-flow joins, and copies/zeros whole or partial aggregates.
Compile it once normally and once with `-d=ssa/decompose_addr/off`; the two executables must
print the same checksum.

Usage: decompose_addr_fuzz.py SEED FUNCTIONS OUTDIR
"""

import os
import random
import subprocess
import sys


HEADER = '''package main

import (
    "fmt"
    "math/bits"
    "runtime"
    "unsafe"
)

'''


def fixed_probes(r):
    """Cases aimed at GC liveness and unsafe aggregate Move partitioning."""
    p, q, n = u64(r), u64(r), u64(r)
    raw = [r.randrange(256) for _ in range(8)]
    return f'''type gcBox struct {{ V uint64 }}

//go:noinline
func gcProbe(cond bool, x uint64) uint64 {{
    type T struct {{ P, Q *gcBox; N uint64 }}
    a := &gcBox{{V: {p}}}
    b := &gcBox{{V: {q}}}
    t := T{{P: a, Q: b, N: {n}}}
    p := &t
    if cond {{
        p.P = p.Q
        p.N += x
    }} else {{
        p.Q = nil
        p.N ^= x
    }}
    a, b = nil, nil
    runtime.GC()
    v := p.N
    if p.P != nil {{ v ^= bits.RotateLeft64(p.P.V, 11) }}
    if p.Q != nil {{ v ^= bits.RotateLeft64(p.Q.V, 37) }}
    runtime.KeepAlive(p)
    return v
}}

//go:noinline
func unsafeMoveProbe(cond bool, x uint64) uint64 {{
    type A [8]uint8
    type B [4]uint16
    // Every source byte is initialized: unlike a padded struct, this remains
    // a deterministic differential oracle while the Move's leaves still have
    // incompatible shapes on its two sides.
    a := A{{{', '.join(str(v) for v in raw)}}}
    b := *(*B)(unsafe.Pointer(&a))
    if cond {{ b[0] += uint16(x); b[3] ^= uint16(x >> 32) }} else {{ b[1] ^= uint16(x); b[2] += uint16(x >> 16) }}
    return uint64(b[0])<<48 ^ uint64(b[1])<<32 ^ uint64(b[2])<<16 ^ uint64(b[3])
}}

'''


def u64(r):
    return r.getrandbits(64)


def nested(i, r):
    j = r.randrange(3)
    ps = [r.randrange(1 << 16) for _ in range(3)]
    qs = [r.randrange(-(1 << 31), 1 << 31) for _ in range(3)]
    c = u64(r)
    ep, eq = r.randrange(1 << 16), r.randrange(-(1 << 31), 1 << 31)
    return f'''//go:noinline
func f{i}(cond bool, x uint64) uint64 {{
    type U struct {{ P uint16; Q int32 }}
    type T struct {{ A uint8; B [3]U; C uint64; D bool }}
    t := T{{A: {r.randrange(256)}, B: [3]U{{{{{ps[0]}, {qs[0]}}}, {{{ps[1]}, {qs[1]}}}, {{{ps[2]}, {qs[2]}}}}}, C: {c}, D: {str(bool(r.randrange(2))).lower()}}}
    p := &t
    q := &p.B[{j}]
    if cond {{
        q.P += uint16(x)
        q.Q ^= int32(x)
        p.C += x
    }} else {{
        *q = U{{P: {ep}, Q: {eq}}}
        p.C ^= x
    }}
    v := *p
    return uint64(v.B[{j}].P) ^ uint64(uint32(v.B[{j}].Q))<<17 ^ v.C
}}

'''


def partial(i, r):
    a, b0, b1, c = r.randrange(1 << 32), r.randrange(1 << 16), r.randrange(1 << 16), u64(r)
    m0, m1 = r.randrange(1 << 16), r.randrange(1 << 16)
    return f'''//go:noinline
func f{i}(cond bool, x uint64) uint64 {{
    type T struct {{ A uint32; B [2]uint16; C uint64 }}
    t := T{{A: {a}, B: [2]uint16{{{b0}, {b1}}}, C: {c}}}
    p := &t.B
    if cond {{
        *p = [2]uint16{{{m0}, uint16(x)}}
    }} else {{
        *p = [2]uint16{{}}
    }}
    v := t
    return uint64(v.A)<<32 ^ uint64(v.B[0])<<16 ^ uint64(v.B[1]) ^ v.C
}}

'''


def string_value(i, r):
    s0 = f"s{r.randrange(1 << 30):x}"
    s1 = f"long-{r.randrange(1 << 62):x}"
    n = u64(r)
    return f'''//go:noinline
func f{i}(cond bool, x uint64) uint64 {{
    type T struct {{ S string; N uint64 }}
    t := T{{S: "{s0}", N: {n}}}
    p := &t
    if cond {{ p.S = "{s1}"; p.N += x }} else {{ p.S = ""; p.N ^= x }}
    v := *p
    return uint64(len(v.S))*0x9e3779b97f4a7c15 ^ v.N
}}

'''


def slice_value(i, r):
    vals = [r.randrange(1 << 16) for _ in range(4)]
    n = u64(r)
    return f'''//go:noinline
func f{i}(cond bool, x uint64) uint64 {{
    type T struct {{ S []uint16; N uint64 }}
    a := [4]uint16{{{vals[0]}, {vals[1]}, {vals[2]}, {vals[3]}}}
    t := T{{S: a[:3:4], N: {n}}}
    p := &t
    if cond {{ p.S = p.S[1:3:3]; p.N += x }} else {{ p.S = p.S[:1:1]; p.N ^= x }}
    v := *p
    return uint64(len(v.S))<<56 ^ uint64(cap(v.S))<<48 ^ uint64(v.S[0]) ^ v.N
}}

'''


def interface_value(i, r):
    a, b, n = r.randrange(-(1 << 31), 1 << 31), r.randrange(-(1 << 31), 1 << 31), u64(r)
    return f'''//go:noinline
func f{i}(cond bool, x uint64) uint64 {{
    type T struct {{ I any; N uint64 }}
    t := T{{I: int64({a}), N: {n}}}
    p := &t
    if cond {{ p.I = int64({b}) + int64(x); p.N += x }} else {{ p.I = int64({a}) - int64(x); p.N ^= x }}
    v := *p
    return uint64(v.I.(int64)) ^ bits.RotateLeft64(v.N, 23)
}}

'''


def complex_value(i, r):
    re0, im0 = r.randrange(-(1 << 20), 1 << 20), r.randrange(-(1 << 20), 1 << 20)
    re1, im1, n = r.randrange(-(1 << 20), 1 << 20), r.randrange(-(1 << 20), 1 << 20), u64(r)
    return f'''//go:noinline
func f{i}(cond bool, x uint64) uint64 {{
    type T struct {{ Z complex128; N uint64 }}
    t := T{{Z: complex({re0}, {im0}), N: {n}}}
    p := &t
    if cond {{ p.Z = complex({re1}, {im1}); p.N += x }} else {{ p.Z += complex(float64(int64(x&255)), -3); p.N ^= x }}
    v := *p
    return uint64(int64(real(v.Z))) ^ uint64(int64(imag(v.Z)))<<21 ^ v.N
}}

'''


def array_value(i, r):
    vals = [r.randrange(1 << 32) for _ in range(4)]
    j, a = r.randrange(4), u64(r)
    return f'''//go:noinline
func f{i}(cond bool, x uint64) uint64 {{
    type T struct {{ V [4]uint32; A uint64 }}
    t := T{{V: [4]uint32{{{vals[0]}, {vals[1]}, {vals[2]}, {vals[3]}}}, A: {a}}}
    p := &t
    q := &p.V[{j}]
    if cond {{ *q += uint32(x); p.A += x }} else {{ *q ^= uint32(x); p.A ^= x }}
    v := *p
    return uint64(v.V[{j}])<<29 ^ v.A
}}

'''


TEMPLATES = [nested, partial, string_value, slice_value, interface_value, complex_value, array_value]


def program(seed, count):
    r = random.Random(seed)
    probes = fixed_probes(r)
    funcs = [r.choice(TEMPLATES)(i, r) for i in range(count)]
    calls = []
    inputs = [0, 1, 2, 255, 256, (1 << 32) - 1, 1 << 32, (1 << 63), (1 << 64) - 1]
    for i in range(count):
        for cond in ("false", "true"):
            x = r.choice(inputs)
            calls.append(f"    h = bits.RotateLeft64(h ^ f{i}({cond}, {x}), 13) * 0x9e3779b97f4a7c15\n")
    calls.append("    h = bits.RotateLeft64(h ^ gcProbe(false, 0xffffffff), 13) * 0x9e3779b97f4a7c15\n")
    calls.append("    h = bits.RotateLeft64(h ^ gcProbe(true, 0x8000000000000000), 13) * 0x9e3779b97f4a7c15\n")
    calls.append("    h = bits.RotateLeft64(h ^ unsafeMoveProbe(false, 0xffff), 13) * 0x9e3779b97f4a7c15\n")
    calls.append("    h = bits.RotateLeft64(h ^ unsafeMoveProbe(true, 0x100000001), 13) * 0x9e3779b97f4a7c15\n")
    r.shuffle(calls)
    return HEADER + probes + "".join(funcs) + "func main() {\n    h := uint64(0x6a09e667f3bcc909)\n" + "".join(calls) + '    fmt.Printf("%016x\\n", h)\n}\n'


def main():
    if len(sys.argv) != 4:
        raise SystemExit(__doc__)
    seed, count, outdir = int(sys.argv[1]), int(sys.argv[2]), sys.argv[3]
    os.makedirs(outdir, exist_ok=True)
    with open(os.path.join(outdir, "go.mod"), "w") as f:
        f.write("module decomposefuzz\ngo 1.25\n")
    path = os.path.join(outdir, "main.go")
    with open(path, "w") as f:
        f.write(program(seed, count))
    go = os.environ.get("GO", "go")
    result = subprocess.run([go, "fmt", "main.go"], cwd=outdir, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stderr)
    print(f"seed {seed}: wrote {count} functions to {path}")


if __name__ == "__main__":
    main()
