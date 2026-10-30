# Changelog

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
- `csplSCFLinearResolution` only tried the first clause as top clause and could miss refutations.
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
