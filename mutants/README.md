# Mutants: deliberately faulty models

Each `.lean` file here is a copy of one `math/bits` model with a single
injected defect, together with the *same* specification theorem as in
`GoInLean/Properties/Bits.lean`. These files are **not** part of the
library build. `scripts/mutation_test.py` compiles each one and requires:

1. the proof attempt to fail with a concrete `bv_decide` counterexample
   (a timeout or any other error is a test failure: "could not prove" is
   not "refuted");
2. the counterexample, turned into a Go test in `go/reproducers/`, to fail
   against the Go mutant in `go/reference/mutants.go` and pass against the
   real `math/bits` function.

This demonstrates success criterion 6 (the pipeline detects deliberately
incorrect implementations) and exercises the counterexample-to-Go path
end to end. Pairing: `<name>.lean` ↔ `reference.<GoName>` is declared in
`mutants/mutants.json`.
