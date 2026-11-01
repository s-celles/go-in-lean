// Package reproducers holds standalone Go tests generated from Lean
// counterexamples (see scripts/mutation_test.py and findings/*/). Each test
// pins the concrete inputs of one counterexample and compares the mutant or
// the real standard-library function against the behavioural oracle.
package reproducers
