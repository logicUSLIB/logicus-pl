module PLNormalFormsClausesTests exposing (suite)

import Dict
import Expect
import Fuzz
import LogicUS.PL.Clauses as CL
import LogicUS.PL.NormalForms as NF
import LogicUS.PL.SyntaxSemantics as SS exposing (FormulaPL(..))
import PLOracle as O
import Set
import Test exposing (Test, describe, fuzz, fuzz2, test)


suite : Test
suite =
    describe "PL.NormalForms and PL.Clauses"
        [ describe "normal forms"
            [ fuzz (O.formula 4) "fplRemoveAllEquiv keeps the meaning and removes ↔" <|
                \f ->
                    let
                        g =
                            NF.fplRemoveAllEquiv f
                    in
                    ( O.equivalent f g, NF.fplContainsEquiv g ) |> Expect.equal ( True, False )
            , fuzz (O.formula 4) "fplRemoveAllImpl keeps the meaning and removes →" <|
                \f ->
                    let
                        g =
                            NF.fplRemoveAllImpl (NF.fplRemoveAllEquiv f)
                    in
                    ( O.equivalent f g, NF.fplContainsImpl g ) |> Expect.equal ( True, False )
            , fuzz (O.formula 4) "fplToNNF is equivalent and in NNF" <|
                \f ->
                    let
                        g =
                            NF.fplToNNF f
                    in
                    ( O.equivalent f g, O.isNNF g ) |> Expect.equal ( True, True ) |> Expect.onFail (SS.fplToString g)
            , fuzz (O.formula 4) "fplToCNF is equivalent and in CNF" <|
                \f ->
                    let
                        g =
                            NF.fplToCNF f
                    in
                    ( O.equivalent f g, O.isCNF g ) |> Expect.equal ( True, True ) |> Expect.onFail (SS.fplToString g)
            , fuzz (O.formula 4) "fplToDNF is equivalent and in DNF" <|
                \f ->
                    let
                        g =
                            NF.fplToDNF f
                    in
                    ( O.equivalent f g, O.isDNF g ) |> Expect.equal ( True, True ) |> Expect.onFail (SS.fplToString g)
            , fuzz (O.formula 4) "fplSatisfiabilityDNF" <|
                \f -> NF.fplSatisfiabilityDNF f |> Expect.equal (O.satisfiable [ f ])
            , fuzz (O.formula 4) "fplValidityCNF" <|
                \f -> NF.fplValidityCNF f |> Expect.equal (not (O.satisfiable [ Neg f ]))
            , fuzz (O.formula 4) "every interpretation from fplModelsDNF is a model" <|
                \f -> NF.fplModelsDNF f |> List.all (\i -> O.eval (Set.fromList i) f) |> Expect.equal True
            , fuzz (O.formula 4) "flpToCNFTseitin is equisatisfiable and in CNF" <|
                \f ->
                    let
                        g =
                            NF.flpToCNFTseitin f
                    in
                    ( Maybe.map O.satisfiableClauses (O.cnfClauses g), O.isCNF g ) |> Expect.equal ( Just (O.satisfiable [ f ]), True )
            ]
        , describe "clauses"
            [ fuzz (O.formula 4) "csplFromCNF (fplToCNF f) has the same models as f" <|
                \f ->
                    case CL.csplFromCNF (NF.fplToCNF f) of
                        Just cs ->
                            O.clausesEquivalentTo [ f ] cs |> Expect.equal True

                        Nothing ->
                            Expect.fail "csplFromCNF returned Nothing for a CNF formula"
            , fuzz (O.formula 4) "fplToClauses has the same models as the formula" <|
                \f -> O.clausesEquivalentTo [ f ] (CL.fplToClauses f) |> Expect.equal True |> Expect.onFail (CL.csplToString (CL.fplToClauses f))
            , fuzz (O.formulaSet 3 3) "splToClauses is equisatisfiable with the set" <|
                \fs -> O.satisfiableClauses (CL.splToClauses fs) |> Expect.equal (O.satisfiable fs) |> Expect.onFail (CL.csplToString (CL.splToClauses fs))
            , fuzz (O.formulaSet 3 3) "splToClauses has the same models as the set" <|
                \fs -> O.clausesEquivalentTo fs (CL.splToClauses fs) |> Expect.equal True |> Expect.onFail (CL.csplToString (CL.splToClauses fs))
            , test "splToClauses on the classroom example gives the classical clausal form" <|
                \_ ->
                    [ "p | q <-> -r", "-p -> s", "-t -> q", "s & t -> u", "-(r -> u)" ]
                        |> List.map SS.fplRead
                        |> CL.splToClauses
                        |> List.length
                        |> Expect.equal 7
            , fuzz (O.formulaSet 4 3) "splToClausesTseitin is equisatisfiable with the set" <|
                \fs -> O.satisfiableClauses (CL.splToClausesTseitin fs) |> Expect.equal (O.satisfiable fs) |> Expect.onFail (CL.csplToString (CL.splToClausesTseitin fs))
            , fuzz (O.formulaSet 4 3) "splToClausesTseitin: every model of the clauses is a model of the set" <|
                \fs ->
                    let
                        cs =
                            CL.splToClausesTseitin fs

                        syms =
                            Set.union (O.clauseSymbols cs) (O.symbolsSet fs)
                    in
                    if Set.size syms > 12 then
                        Expect.pass

                    else
                        O.interpretations syms
                            |> List.all (\i -> not (O.evalClauseSet i cs) || O.evalSet i fs)
                            |> Expect.equal True
            , test "splToClausesTseitin: the counterexample of 4.0.0 stays satisfiable" <|
                \_ ->
                    [ "(p & q) | r", "(-p & -q) | r", "p & q" ]
                        |> List.map SS.fplRead
                        |> CL.splToClausesTseitin
                        |> O.satisfiableClauses
                        |> Expect.equal True
            , test "documented example of fplToClauses" <|
                \_ ->
                    SS.fplRead "¬p & q <-> r"
                        |> CL.fplToClauses
                        |> Expect.equal [ [ ( ( "p", [] ), True ), ( ( "r", [] ), True ), ( ( "q", [] ), False ) ], [ ( ( "p", [] ), False ), ( ( "r", [] ), False ) ], [ ( ( "q", [] ), True ), ( ( "r", [] ), False ) ] ]
            , test "documented example of splToClauses" <|
                \_ ->
                    [ "p->q", "p | q -> r", "¬p | q" ]
                        |> List.map SS.fplRead
                        |> CL.splToClauses
                        |> Expect.equal [ [ ( ( "q", [] ), True ), ( ( "p", [] ), False ) ], [ ( ( "r", [] ), True ), ( ( "p", [] ), False ) ], [ ( ( "r", [] ), True ), ( ( "q", [] ), False ) ] ]
            , fuzz O.clauseSet "csplIsSat / csplIsInsat" <|
                \cs -> ( CL.csplIsSat cs, CL.csplIsInsat cs ) |> Expect.equal ( O.satisfiableClauses cs, not (O.satisfiableClauses cs) )
            , fuzz O.clauseSet "csplModels are exactly the models" <|
                \cs ->
                    CL.csplModels cs
                        |> O.toSet
                        |> Expect.equal
                            (O.interpretations (O.clauseSymbols cs)
                                |> List.filter (\i -> O.evalClauseSet i cs)
                                |> List.map Set.toList
                                |> Set.fromList
                            )
            , fuzz O.clauseSet "csplIsTaut" <|
                \cs ->
                    CL.csplIsTaut cs
                        |> Expect.equal (List.all (\i -> O.evalClauseSet i cs) (O.interpretations (O.clauseSymbols cs)))
            , fuzz O.clauseSet "csplRemoveSubsumedClauses keeps the models" <|
                \cs -> O.clausesEquivalentTo [ SS.splConjunction (List.map clauseToFormula cs) ] (CL.csplRemoveSubsumedClauses cs) |> Expect.equal True
            , fuzz O.clauseSet "csplRemoveTautClauses keeps the models" <|
                \cs -> O.clausesEquivalentTo [ SS.splConjunction (List.map clauseToFormula cs) ] (CL.csplRemoveTautClauses cs) |> Expect.equal True
            , fuzz2 O.clause O.clause "cplSubsumes c1 c2 implies c1 ⊨ c2" <|
                \c1 c2 ->
                    if CL.cplSubsumes c1 c2 then
                        O.entails [ clauseToFormula c1 ] (clauseToFormula c2) |> Expect.equal True

                    else
                        Expect.pass
            , fuzz O.clause "cplRead (cplToInputString c) gives back the same clause" <|
                \c -> CL.cplRead (CL.cplToInputString c) |> CL.cplSort |> Expect.equal (CL.cplSort (dedup c))
            , fuzz O.clauseSet "csplToDIMACS encodes the same clauses" <|
                \cs ->
                    let
                        ( txt, dict ) =
                            CL.csplToDIMACS cs

                        decoded =
                            txt
                                |> String.lines
                                |> List.filter (\l -> not (String.startsWith "c" l) && not (String.startsWith "p" l) && String.trim l /= "")
                                |> List.map
                                    (\l ->
                                        String.words l
                                            |> List.filterMap String.toInt
                                            |> List.filter ((/=) 0)
                                            |> List.filterMap (\n -> Maybe.map (\s -> ( s, n > 0 )) (Dict.get (abs n) dict))
                                    )
                    in
                    O.clausesEquivalentTo [ SS.splConjunction (List.map clauseToFormula cs) ] decoded |> Expect.equal True |> Expect.onFail txt
            ]
        ]


clauseToFormula : CL.ClausePL -> FormulaPL
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


dedup : CL.ClausePL -> CL.ClausePL
dedup c =
    List.foldl
        (\x acc ->
            if List.member x acc then
                acc

            else
                acc ++ [ x ]
        )
        []
        c
