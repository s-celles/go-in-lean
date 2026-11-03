#!/usr/bin/env python3
"""Consistency lint for SSA OpcodeTable flags annotations (_gen/*Ops.go).

An op whose assembly instruction writes the machine flags register *as a side effect*
must be declared `clobberFlags: true`, otherwise flagalloc believes a flag value survives
the instruction and a later flag consumer (SETcc, a carry mask, a branch) can read the
clobbered flags instead of a regenerated copy (the defect class of golang/go#82825,
SBBQcarrymask/SBBLcarrymask unmarked on 386/AMD64; also golang/go#81842 ppc64x and
golang/go#21080 s390x).

Ops whose *result is the flags value* (reg class ending in `flags`: CMP, TEST, UCOMIS...)
are flag definitions, not clobberers, and are excluded. Calls imply clobberFlags.

Checks:

  A. x86 flag writers: on 386/AMD64, an op whose base asm mnemonic writes flags
     (add/sub/adc/sbb/neg/mul/imul/and/or/xor/test/cmp/shl/shr/sar/rol/ror/shlx/shrx/
     sarx/bsf/bsr/bt*/popcnt/inc/dec/ucomis/comis), is not a flag definition, and is
     not marked clobberFlags.
  B. mnemonic asymmetry: within one Ops.go file, ops sharing an asm base mnemonic (size
     suffix ignored) with inconsistent clobberFlags - a family that forgot one variant.
     Flag definitions are excluded.
  C. flag consumers producing a register (all arches): an op whose reg class takes
     flags and produces a general-purpose value (`flagsgp`/`carry` classes) with an asm
     that performs an ALU operation also writes flags; unmarked ones are reported.

Output: candidates, not findings; each must be triaged by hand (semantics, reachability).
Usage: ops_clobber_lint.py GEN_DIR [file.Ops.go ...]
"""
import os, re, sys
from collections import defaultdict

X86_FLAG_WRITERS = {
    "ADD", "SUB", "ADC", "SBB", "NEG", "INC", "DEC",
    "MUL", "IMUL",
    "AND", "OR", "XOR", "TEST", "CMP",
    "SHL", "SAL", "SHR", "SAR", "ROL", "ROR", "RCL", "RCR",
    "SHLX", "SHRX", "SARX",
    "BSF", "BSR", "BT", "BTS", "BTR", "BTC",
    "POPCNT", "UCOMIS", "COMIS", "FTST",
}

OP_LINE = re.compile(r'\{name:\s*"([^"]+)"(.*)')

def fields(line):
    asm = re.search(r'\basm:\s*"([^"]+)"', line)
    reg = re.search(r'\breg:\s*(\w+)', line)
    reg = reg.group(1) if reg else None
    return {
        "clobber": "clobberFlags: true" in line,
        "call": "call: true" in line,
        "asm": asm.group(1) if asm else None,
        "reg": reg,
        # a reg class ending in "flags" produces the flags value (gp1flags, fp2flags...)
        "flag_def": bool(reg) and reg.endswith("flags") and "carry" not in reg,
    }

def base_mnem(asm):
    """Size suffix and go suffix stripped mnemonic: ADDQ->ADD, CMPLconst->CMP, SBBQ->SBB."""
    m = asm
    m = re.sub(r"^([A-Z0-9]+?)const$", r"\1", m)      # CMPLconst -> CMPL
    m = re.sub(r"^([A-Z0-9]+?)[WLQ]$", r"\1", m)      # CMPL -> CMP, ADDQ -> ADD
    if not asm.startswith("SET"):                      # never strip SETEQ -> SETE
        m = re.sub(r"^([A-Z0-9]+?)const$", r"\1", m)
        m = re.sub(r"^([A-Z0-9]+?)[WLQ]$", r"\1", m)
    return m

def main():
    d = sys.argv[1]
    files = sys.argv[2:] or sorted(f for f in os.listdir(d) if f.endswith("Ops.go"))
    hits = 0
    for f in files:
        path = os.path.join(d, f)
        x86 = f.startswith(("386", "AMD64"))
        ops = []
        for ln, line in enumerate(open(path), 1):
            m = OP_LINE.search(line)
            if not m:
                continue
            fl = fields(line)
            if fl["call"]:
                continue
            ops.append((ln, m.group(1), fl))
        for ln, name, fl in ops:
            if not fl["asm"] or fl["flag_def"] or fl["clobber"]:
                continue
            bm = base_mnem(fl["asm"])
            takes_flags = bool(fl["reg"]) and (
                fl["reg"].startswith("flags") or "carry" in fl["reg"] or fl["reg"] == "readflags"
            )
            if x86 and bm in X86_FLAG_WRITERS:
                print(f"A {f}:{ln}: {name} asm={fl['asm']} reg={fl['reg']} writes flags, not clobberFlags")
                hits += 1
            elif takes_flags and bm not in ("MOV", "MOVB", "MOVW", "MOVL", "MOVQ"):
                print(f"C {f}:{ln}: {name} asm={fl['asm']} reg={fl['reg']} consumes flags, "
                      f"ALU result, not clobberFlags")
                hits += 1
        byasm = defaultdict(list)
        for ln, name, fl in ops:
            if fl["asm"] and not fl["flag_def"]:
                byasm[base_mnem(fl["asm"])].append((ln, name, fl["clobber"]))
        for bm, group in sorted(byasm.items()):
            if len(group) < 2:
                continue
            marks = {c for _, _, c in group}
            if marks == {True, False}:
                for ln, name, c in group:
                    if not c:
                        print(f"B {f}:{ln}: {name} asm={bm} family mixed; marked: "
                              + ", ".join(n for _, n, c2 in group if c2)[:90])
                        hits += 1
    print(f"{hits} candidates")

if __name__ == "__main__":
    main()
