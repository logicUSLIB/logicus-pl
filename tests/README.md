# Tests

Semantic tests: every algorithm is checked against a reference implementation written
independently of the library (`PLOracle.elm`), on random formulas and clause sets.
`PLRegressionTests.elm` keeps one test per bug found, with its counterexample.

Run them with [elm-test](https://github.com/rtfeldman/node-test-runner):

    npx elm-test
