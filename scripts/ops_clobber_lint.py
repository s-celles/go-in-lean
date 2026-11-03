#!/usr/bin/env python3
"""Consistency lint for SSA OpcodeTable flags annotations (_gen/*Ops.go).

An op whose assembly instruction writes the machine flags register *as a side
effect* must be declared `clobberFlags: true`, otherwise flagalloc believes a
flag value survives the instruction and a later flag consumer (SETcc, a carry
mask, a branch) can read the clobbered flags instead of a regenerated copy (the
defect class of golang/go#82825, SBBQcarrymask/SBBLcarrymask unmarked on
386/AMD64; also golang/go#81842 ppc64x and golang/go#21080 s390x).

Flag producers are excluded: an op that *outputs* a flags value - a CMP/TEST
flag definition, or a <carry,result> tuple such as 386 ADDLcarry, ARM ADDS or
PPC64 ANDCC - overwrites the flags register as its own definition, which
flagalloc already models (Value.ClobbersFlags() returns true for tuples with a
flags field, and flag defs invalidate the cached register state). Instructions
that provably leave the flags unaffected are also excluded: x86 BMI2
SHLX/SHRX/SARX, SETcc and CSEL/CSINC/ISEL flag readers, and plain MOV.

Checks:

  A. x86 flag writers: on 386/AMD64, an op whose base asm mnemonic writes flags
     (add/sub/adc/sbb/neg/mul/imul/and/or/xor/test/cmp/shl/shr/sar/rol/ror/
     bsf/bsr/bt*/popcnt/ucomis/comis), is not a flag producer, and is not
     marked clobberFlags.
  B. mnemonic asymmetry: within one Ops.go file, ops sharing an asm base
     mnemonic (size suffix ignored) with inconsistent clobberFlags - a family
     that forgot one variant. Flag producers are excluded, and so are the
     MOV/SET families whose instructions never write flags.
  C. flag consumers producing a register (all arches): an op that consumes a
     flags value and produces a general-purpose one (`flagsgp`-style regs,
     carry/cr inputs) with an asm that performs a flags-writing ALU operation;
     unmarked ones are reported.

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
    "BSF", "BSR", "BT", "BTS", "BTR", "BTC",
    "POPCNT", "UCOMIS", "COMIS", "FTST",
    "CMPXCHG",
}
# SHLX/SHRX/SARX (BMI2) are deliberately absent: they leave the flags unaffected.

# Base mnemonics of instructions that read the flags but never write them, and
# of families whose marking is conservative noise (plain MOV, SETcc). ADC/SBC
# read-only here: on ARM/ARM64 they consume C without writing flags (the S
# variants are separate ops); on 386/AMD64 the A check catches them first
# because x86 ADC/SBB always write flags.
FLAG_READER_ASM = ("SET", "CSEL", "CSINC", "CSINV", "CSNEG", "CSET", "ISEL",
                   "CMOV", "READF", "ADC", "SBC", "RSC", "NGC", "SRA", "LOCGR")
NEVER_WRITES_ASM = ("MOV", "SET")

OP_LINE = re.compile(r'\{name:\s*"([^"]+)"(.*)')
# A reg whose trailing class is a flags value (possibly a load variant):
# gp1flags, gp1flagsLoad, gp21carry, fp2cr - the op defines a flags value.
FLAG_PRODUCER_RE = re.compile(r"(flags|carry|cr)(Load|idx\d+)?$")
# A flags value consumed as a non-trailing input: gp2flags1 (ADCL), gp2carry1,
# crgp21 (ISEL), or a leading flags input class (flagsgp = SETcc).
FLAG_CONSUMER_RE = re.compile(r"^(flags|fp\d*cr)|((flags|carry|cr)\d)")

def fields(line):
    asm = re.search(r'\basm:\s*"([^"]+)"', line)
    reg = re.search(r'\breg:\s*(\w+)', line)
    reg = reg.group(1) if reg else None
    typ = re.search(r'\btyp:\s*"([^"]+)"', line)
    typ = typ.group(1) if typ else None
    return {
        "clobber": "clobberFlags: true" in line,
        "call": "call: true" in line,
        "asm": asm.group(1) if asm else None,
        "reg": reg,
        # the op outputs a flags value: a trailing flags/carry/cr reg class
        # (x86 readflags only *stores* the flags, it does not define them),
        # or a typ tuple with a Flags field (PPC64 ANDCC).
        "flag_def": (reg is not None and reg != "readflags"
                     and bool(FLAG_PRODUCER_RE.search(reg)))
                    or (typ is not None and "Flags" in typ),
        # the op consumes a flags value: a flags/carry/cr input encoded as a
        # non-trailing class, a leading flags input, or x86 readflags.
        "flag_use": reg is not None and (reg == "readflags"
                                         or bool(FLAG_CONSUMER_RE.search(reg))),
    }

def base_mnem(asm):
    """Size suffix and go suffix stripped mnemonic: ADDQ->ADD, CMPLconst->CMP, SBBQ->SBB."""
    if asm.startswith("SET"):                      # never strip SETEQ -> SETE
        return asm
    m = re.sub(r"^([A-Z0-9]+?)const$", r"\1", asm)  # CMPLconst -> CMPL
    m = re.sub(r"^([A-Z0-9]+?)[WLQ]$", r"\1", m)    # CMPL -> CMP, ADDQ -> ADD
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
            if x86 and bm in X86_FLAG_WRITERS:
                print(f"A {f}:{ln}: {name} asm={fl['asm']} reg={fl['reg']} writes flags, not clobberFlags")
                hits += 1
            elif (fl["flag_use"] and not fl["asm"].startswith(FLAG_READER_ASM)
                  and not bm.startswith("MOV")):
                print(f"C {f}:{ln}: {name} asm={fl['asm']} reg={fl['reg']} consumes flags, "
                      f"ALU result, not clobberFlags")
                hits += 1
        byasm = defaultdict(list)
        for ln, name, fl in ops:
            if fl["asm"] and not fl["flag_def"]:
                byasm[base_mnem(fl["asm"])].append((ln, name, fl["clobber"]))
        for bm, group in sorted(byasm.items()):
            if bm.startswith(NEVER_WRITES_ASM):
                continue
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
