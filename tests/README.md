# Tests

Semantic tests: every algorithm is checked against a reference implementation written
independently of the library (`PLOracle.elm`), on random formulas and clause sets.
`PLRegressionTests.elm` keeps one test per bug found, with its counterexample.
`PLDeductionTests.elm` checks the deduction systems: textbook proofs are accepted, each kind of
error is rejected, every step that the checker accepts is valid and every correct instance of a rule
is accepted (random instances, checked with truth tables), the hints only propose correct lines, and
a rule has a counterexample exactly when it is not valid.

Run them with [elm-test](https://github.com/rtfeldman/node-test-runner):

    npx elm-test
