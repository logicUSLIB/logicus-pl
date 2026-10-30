module PLRegressionTests exposing (suite)

{-| One test per bug found in the October 2026 review, with the concrete
counterexample that exposed it.
-}

import Expect
import LogicUS.PL.CSP as CSP
import LogicUS.PL.Clauses as CL
import LogicUS.PL.NormalForms as NF
import LogicUS.PL.Resolution as R
import LogicUS.PL.SyntaxSemantics as SS exposing (FormulaPL(..))
import PLOracle as O
import Test exposing (Test, describe, test)


p : FormulaPL
p =
    Atom ( "p", [] )


q : FormulaPL
q =
    Atom ( "q", [] )


suite : Test
suite =
    describe "PL regressions"
        [ test "splToClauses: satisfiable set stays satisfiable (Tseitin symbols collided across formulas in 4.0.0)" <|
            \_ ->
                [ "(p & q) | r", "(-p & -q) | r", "p & q" ]
                    |> List.map SS.fplRead
                    |> CL.splToClauses
                    |> O.satisfiableClauses
                    |> Expect.equal True
        , test "logicalConsecuence: p does not entail ¬q (symbols only in the goal were ignored)" <|
            \_ -> SS.logicalConsecuence [ p ] (Neg q) |> Expect.equal False
        , test "logicalConsecuence: ⊤ does not entail ¬p" <|
            \_ -> SS.logicalConsecuence [ Taut ] (Neg p) |> Expect.equal False
        , test "fplSatisfiabilityDNF: ⊥ ∧ ⊥ is unsatisfiable (⊥ inside a conjunction was ignored)" <|
            \_ -> NF.fplSatisfiabilityDNF (Conj Insat Insat) |> Expect.equal False
        , test "fplValidityCNF: ⊤ ∧ (p ∨ ⊤) is valid (⊤ inside a clause was ignored)" <|
            \_ -> NF.fplValidityCNF (Conj Taut (Disj p Taut)) |> Expect.equal True
        , test "csplFromCNF: p ∨ ⊤ gives no clauses" <|
            \_ -> CL.csplFromCNF (Disj p Taut) |> Expect.equal (Just [])
        , test "csplFromCNF: ⊥ gives the empty clause" <|
            \_ -> CL.csplFromCNF Insat |> Expect.equal (Just [ [] ])
        , test "Tseitin: {p ∧ ⊤, ¬⊥} is satisfiable (¬⊥ was mistranslated)" <|
            \_ -> CL.splToClausesTseitin [ Conj p Taut, Neg Insat ] |> O.satisfiableClauses |> Expect.equal True
        , test "CSP.solver: {p}, {¬p} is unsatisfiable (contradictory unit clauses were propagated together)" <|
            \_ -> CSP.solver [ [ ( ( "p", [] ), True ) ], [ ( ( "p", [] ), False ) ] ] |> Tuple.first |> Expect.equal False
        , test "linear resolution: {p}, {p}, {¬q}, {q} is refuted (only the first clause was tried as top clause)" <|
            \_ ->
                R.csplSCFLinearResolution [ [ ( ( "p", [] ), True ) ], [ ( ( "p", [] ), True ) ], [ ( ( "q", [] ), False ) ], [ ( ( "q", [] ), True ) ] ]
                    |> Tuple.first
                    |> Expect.equal True
        , test "saturation resolution terminates on a satisfiable set (it recomputed known resolvents forever)" <|
            \_ ->
                R.csplSaturationResolution [ [ ( ( "p", [] ), True ), ( ( "q", [] ), True ) ], [ ( ( "p", [] ), False ), ( ( "q", [] ), True ) ] ]
                    |> Tuple.first
                    |> Expect.equal False
        , test "every resolution method refutes an input that already has the empty clause" <|
            \_ ->
                [ R.csplSCFResolution [ [], [ ( ( "p", [] ), True ) ] ] |> Tuple.first
                , R.csplSCFLinearResolution [ [], [ ( ( "p", [] ), True ) ] ] |> Tuple.first
                , R.csplSCFPositiveResolution [ [], [ ( ( "p", [] ), True ) ] ] |> Tuple.first
                , R.csplSCFNegativeResolution [ [], [ ( ( "p", [] ), True ) ] ] |> Tuple.first
                , R.csplSCFUnitaryResolution [ [], [ ( ( "p", [] ), True ) ] ] |> Tuple.first
                , R.csplSCFByEntriesResolution [ [], [ ( ( "p", [] ), True ) ] ] |> Tuple.first
                ]
                    |> Expect.equal (List.repeat 6 True)
        , test "cplRead removes repeated literals" <|
            \_ -> CL.cplRead "{¬p, ¬p}" |> Expect.equal [ ( ( "p", [] ), False ) ]
        , test "parser errors are readable" <|
            \_ ->
                SS.fplReadFromString "(p | q"
                    |> (\( _, _, msg ) -> msg)
                    |> Expect.equal "Syntax error after \"(p|q\": expected ')'"
        ]
