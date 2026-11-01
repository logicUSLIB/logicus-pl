# Changelog

## 4.2.0

### Added

- `LogicUS.PL.Deduction`: deduction systems given by their rules, and proofs checked with them.
  - Rules are schemas: capital letters stand for formulas and a premise `[A] B` is a subproof that the rule closes.
    Axioms are rules without premises. `readSystem` reads a rule per line and `systemToString` writes them back.
    Rules with quantifiers, substitutions or side conditions are rejected with a message that says they are for
    first-order logic.
  - `ruleCounterexample` gives a valuation of the letters of a rule under which its premises are true and its
    conclusion false (a subproof `[A] B` counts as `A → B`); there is none exactly when the rule is valid.
  - Proofs are written in the style of Fitch (a line per formula, a bar per open subproof, `premise`, `assumption`
    or a rule and the lines or subproofs it cites). `checkProof` checks each line with the rules of the system (the
    cited lines may be in any order) and explains each error: a rule that does not give the formula, a rule that is
    not in the system, a line that is below or inside a closed subproof, a subproof cited by part, a premise that is
    not one of the exercise, a proof that ends inside a subproof or without the goal.
  - `hints` gives the rules that can be used at the end of a proof: applied to the lines that can be cited, closing
    the current subproof, or giving the goal (or a target) from what is still needed. Every suggested line is
    accepted by `checkProof`.
- `LogicUS.PL.DeductionSystems`: natural deduction (intuitionistic and classical rules, derived rules such as MT, DS,
  HS and De Morgan laws) and Łukasiewicz's axiomatic system, as text that can be edited.

## 4.1.0

Correctness fixes found by a new suite of semantic tests (`tests/`), which compares every
algorithm with truth tables computed independently of the library.

### Fixed

- `splToClauses` and `fplToClauses` use the classical CNF again, so the clause set has the same
  models as the formulas. In 4.0.0 they used the Tseitin transformation formula by formula, and the
  fresh symbols `𝜏ᵢ` of different formulas collided: a satisfiable set such as
  `{(p∧q)∨r, (¬p∧¬q)∨r, p∧q}` could become an unsatisfiable clause set.
- `logicalConsecuence` ignored the symbols that occur only in the conclusion: `{p} ⊨ ¬q` was
  reported as true.
- ⊤ and ⊥ inside clauses and conjunctions were dropped instead of absorbing or being neutral, in
  `csplFromCNF`, `cnfAsLiteralSets`, `dnfAsLiteralSets`, `fplSatisfiabilityDNF`, `fplValidityCNF`
  and `fplModelsDNF` (e.g. `⊥ ∧ ⊥` was reported satisfiable).
- `CSP.solver` (and `sbfplsolver`) propagated all unit clauses at once, so `{p}, {¬p}` was reported
  satisfiable.
- `csplSCFLinearResolution` only tried the first clause as top clause and could miss refutations; it also explored
  every branch after finding a refutation.
- An input containing the empty clause was reported satisfiable by the graph-based resolution functions.
- `csplSaturationResolution` did not terminate on satisfiable sets.
- `cplReadFromString` keeps each literal once.
- Parser error messages no longer show internal Elm values: they say what was read and what was
  expected, e.g. `Syntax error after "(p|q": expected ')'`.

### Added

- `NormalForms.fplToCNFTseitin` and `NormalForms.splToCNFTseitin`: Tseitin transformation with the
  fresh symbols shared by the whole set (equisatisfiable, linear size).
- `Clauses.fplToClausesTseitin` and `Clauses.splToClausesTseitin`.

### Deprecated

- `NormalForms.flpToCNFTseitin` (misspelled): use `fplToCNFTseitin`.
