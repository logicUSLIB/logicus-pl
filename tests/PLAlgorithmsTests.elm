module PLAlgorithmsTests exposing (suite)

import Expect
import Fuzz exposing (Fuzzer)
import Graph
import LogicUS.PL.CSP as CSP
import LogicUS.PL.Clauses as CL exposing (ClausePL, ClausePLSet)
import LogicUS.PL.DPLL as DPLL
import LogicUS.PL.HornRS as H
import LogicUS.PL.Resolution as R
import LogicUS.PL.SemanticTableaux as ST
import LogicUS.PL.SyntaxSemantics as SS exposing (FormulaPL(..))
import PLOracle as O
import Set exposing (Set)
import Test exposing (Test, describe, fuzz, test)


suite : Test
suite =
    describe "PL algorithms"
        [ describe "DPLL"
            [ fuzz O.clauseSet "finds a model iff the clause set is satisfiable" <|
                \cs ->
                    dpllModels cs |> List.isEmpty |> not |> Expect.equal (O.satisfiableClauses cs)
            , fuzz O.clauseSet "every model it gives satisfies the clauses" <|
                \cs -> dpllModels cs |> List.all (\i -> O.evalClauseSet (Set.fromList i) cs) |> Expect.equal True
            ]
        , describe "resolution (True = unsatisfiable)"
            [ fuzz O.clauseSet "saturation" <|
                \cs -> Tuple.first (R.csplSaturationResolution cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz O.clauseSet "regular (Davis–Putnam)" <|
                \cs -> Tuple.first (R.csplRegularResolution (Set.toList (O.clauseSymbols cs)) cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz O.clauseSet "shortest clause first" <|
                \cs -> Tuple.first (R.csplSCFResolution cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz O.clauseSet "linear" <|
                \cs -> Tuple.first (R.csplSCFLinearResolution cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz O.clauseSet "positive" <|
                \cs -> Tuple.first (R.csplSCFPositiveResolution cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz O.clauseSet "negative" <|
                \cs -> Tuple.first (R.csplSCFNegativeResolution cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz hornClauseSet "unit resolution is complete for Horn clauses" <|
                \cs -> Tuple.first (R.csplSCFUnitaryResolution cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz hornClauseSet "input (by entries) resolution is complete for Horn clauses" <|
                \cs -> Tuple.first (R.csplSCFByEntriesResolution cs) |> Expect.equal (not (O.satisfiableClauses cs))
            , fuzz O.clauseSet "unit resolution is sound on any clause set" <|
                \cs -> soundVerdict (Tuple.first (R.csplSCFUnitaryResolution cs)) cs
            , fuzz O.clauseSet "input resolution is sound on any clause set" <|
                \cs -> soundVerdict (Tuple.first (R.csplSCFByEntriesResolution cs)) cs
            , fuzz O.clauseSet "every clause in the SCF resolution graph follows from the input" <|
                \cs -> R.csplSCFResolution cs |> Tuple.second |> graphClauses |> allEntailed cs
            , fuzz O.clauseSet "every clause in the linear resolution graph follows from the input" <|
                \cs -> R.csplSCFLinearResolution cs |> Tuple.second |> graphClauses |> allEntailed cs
            , fuzz O.clauseSet "every clause produced by saturation follows from the input" <|
                \cs -> R.csplSaturationResolution cs |> Tuple.second |> List.concat |> allEntailed cs
            ]
        , describe "semantic tableaux"
            [ fuzz (O.formulaSet 3 3) "has an open branch iff the set is satisfiable" <|
                \fs -> ST.semanticTableau fs |> ST.semanticTableauOpenLeaves |> List.isEmpty |> not |> Expect.equal (O.satisfiable fs)
            , fuzz (O.formulaSet 3 3) "gives models iff the set is satisfiable" <|
                \fs -> ST.semanticTableau fs |> ST.semanticTableauModels |> List.isEmpty |> not |> Expect.equal (O.satisfiable fs)
            , fuzz (O.formulaSet 3 3) "every model it gives satisfies the set" <|
                \fs -> ST.semanticTableau fs |> ST.semanticTableauModels |> List.all (\i -> O.evalSet (Set.fromList i) fs) |> Expect.equal True
            ]
        , describe "Horn reasoning systems"
            [ fuzz hornProblem "forwardChaining1 reaches the goal iff it is entailed" <|
                \( rules, kb, goal ) -> (H.forwardChaining1 rules kb goal).res |> Expect.equal (hornEntails rules kb goal)
            , fuzz hornProblem "forwardChaining2 reaches the goal iff it is entailed" <|
                \( rules, kb, goal ) -> (H.forwardChaining2 rules kb goal).res |> Expect.equal (hornEntails rules kb goal)
            , fuzz hornProblem "backwardChaining1 reaches the goal iff it is entailed" <|
                \( rules, kb, goal ) -> (H.backwardChaining1 rules kb goal).res |> Expect.equal (hornEntails rules kb goal)
            , fuzz hornProblem "hornRulesToSPL and hornKBToSPL agree with chaining" <|
                \( rules, kb, goal ) ->
                    O.entails (H.hornRulesToSPL rules ++ H.hornKBToSPL kb) (Atom goal) |> Expect.equal (hornEntails rules kb goal)
            ]
        , describe "CSP solver"
            [ fuzz O.clauseSet "solver decides satisfiability" <|
                \cs -> Tuple.first (CSP.solver cs) |> Expect.equal (O.satisfiableClauses cs)
            , fuzz O.clauseSet "solver's model satisfies the clauses" <|
                \cs ->
                    case CSP.solver cs of
                        ( True, model ) ->
                            O.evalClauseSet (Set.fromList model) cs |> Expect.equal True

                        _ ->
                            Expect.pass
            ]
        ]



-- HELPERS


dpllModels : ClausePLSet -> List (List SS.PSymb)
dpllModels cs =
    DPLL.dpllTableauModels (Set.toList (O.clauseSymbols cs)) (DPLL.dpll cs)


soundVerdict : Bool -> ClausePLSet -> Expect.Expectation
soundVerdict unsat cs =
    if unsat then
        O.satisfiableClauses cs |> Expect.equal False

    else
        Expect.pass


graphClauses : Graph.Graph ( Bool, ClausePL ) e -> List ClausePL
graphClauses g =
    Graph.nodes g |> List.map (.label >> Tuple.second)


clauseToFormula : ClausePL -> FormulaPL
clauseToFormula c =
    case c of
        [] ->
            Insat

        _ ->
            SS.splDisjunction
                (List.map
                    (\( a, pol ) ->
                        if pol then
                            Atom a

                        else
                            Neg (Atom a)
                    )
                    c
                )


allEntailed : ClausePLSet -> List ClausePL -> Expect.Expectation
allEntailed cs derived =
    let
        premises =
            List.map clauseToFormula cs

        bad =
            List.filter (\c -> not (O.entails premises (clauseToFormula c))) derived
    in
    bad |> Expect.equal []


{-| Horn clause sets: at most one positive literal per clause.
-}
hornClauseSet : Fuzzer ClausePLSet
hornClauseSet =
    let
        hornClause =
            Fuzz.map2
                (\negs pos ->
                    List.map (\a -> ( a, False )) negs
                        ++ (case pos of
                                Just a ->
                                    [ ( a, True ) ]

                                Nothing ->
                                    []
                           )
                )
                (Fuzz.listOfLengthBetween 0 2 (Fuzz.oneOfValues O.atoms))
                (Fuzz.maybe (Fuzz.oneOfValues O.atoms))
                |> Fuzz.filter (not << List.isEmpty)
    in
    Fuzz.listOfLengthBetween 1 7 hornClause


hornFacts : List H.HornFact
hornFacts =
    [ ( "P", [] ), ( "Q", [] ), ( "R", [] ), ( "S", [] ), ( "T", [] ) ]


hornProblem : Fuzzer ( List H.HornRule, H.HornKB, H.HornFact )
hornProblem =
    let
        rule =
            Fuzz.map2 (\body head -> ( Set.fromList body, head ))
                (Fuzz.listOfLengthBetween 1 3 (Fuzz.oneOfValues hornFacts))
                (Fuzz.oneOfValues hornFacts)
    in
    Fuzz.triple
        (Fuzz.listOfLengthBetween 0 6 rule)
        (Fuzz.map Set.fromList (Fuzz.listOfLengthBetween 0 3 (Fuzz.oneOfValues hornFacts)))
        (Fuzz.oneOfValues hornFacts)


{-| Least model of the definite program, computed by naive iteration.
-}
hornEntails : List H.HornRule -> H.HornKB -> H.HornFact -> Bool
hornEntails rules kb goal =
    let
        step known =
            List.foldl
                (\( body, head ) acc ->
                    if Set.isEmpty (Set.diff body acc) then
                        Set.insert head acc

                    else
                        acc
                )
                known
                rules

        fix known =
            let
                next =
                    step known
            in
            if next == known then
                known

            else
                fix next
    in
    Set.member goal (fix kb)
