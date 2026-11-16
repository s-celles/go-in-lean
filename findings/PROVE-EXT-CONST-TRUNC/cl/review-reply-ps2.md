<!-- Draft replies for CL 858581 patchset 2, answering Keith Randall's 2026-11-13 comments. Posted on 2026-11-16 as written: the two inline replies on patchset 1 threads, the top-level message on patchset 2. -->

## prove.go line 873 ("b certainly sounds better to me")

Done in PS2. The extension case is unchanged; the x+delta case now does the
constant computation only when w fits in x's type, with the explanation there.

## prove.go line 2830 (comment placement)

Done: constFitsIn is replaced by fitsSigned, whose comment only says what it
does. The reason for the check is at the caller, in the x+delta case.

## Top-level message

PS2 moves the check into the x+delta constant case, as suggested. The
regression test is unchanged. It fails with go1.27.4 and passes with this
patchset. test/prove*.go, loopbce, checkbce, codegen and fixedbugs pass, and so
do the short cmd/compile/internal/ssa and ssacompile tests.

Assisted by AI.
