module PLSyntaxSemanticsTests exposing (suite)

import Expect
import Fuzz
import LogicUS.PL.SyntaxSemantics as SS exposing (FormulaPL(..))
import PLOracle as O
import Set
import Test exposing (Test, describe, fuzz, fuzz2, test)


suite : Test
suite =
    describe "PL.SyntaxSemantics"
        [ describe "parser"
            [ fuzz (O.formula 4) "fplRead (fplToInputString f) is equivalent to f" <|
                \f ->
                    let
                        g =
                            SS.fplRead (SS.fplToInputString f)
                    in
                    O.equivalent f g
                        |> Expect.equal True
                        |> Expect.onFail ("input string: " ++ SS.fplToInputString f ++ "  read back: " ++ SS.fplToString g)
            , fuzz (O.formula 4) "fplRead (fplToInputString f) == f (structurally)" <|
                \f -> SS.fplRead (SS.fplToInputString f) |> Expect.equal f
            , test "reads the usual ASCII and Unicode connectives" <|
                \_ ->
                    [ "p & q", "p ∧ q", "p | q", "p ∨ q", "p -> q", "p → q", "p <-> q", "p ↔ q", "-p", "¬p", "!T", "!F" ]
                        |> List.map (SS.fplReadFromString >> (\( m, _, _ ) -> m /= Nothing))
                        |> Expect.equal (List.repeat 12 True)
            , test "rejects malformed input" <|
                \_ ->
                    [ "p &", "(p | q", "p & & q", "" ]
                        |> List.map (SS.fplReadFromString >> (\( m, _, _ ) -> m == Nothing))
                        |> Expect.equal [ True, True, True, True ]
            , test "the error message does not expose internal Elm values" <|
                \_ ->
                    let
                        ( _, _, msg ) =
                            SS.fplReadFromString "(p | q"
                    in
                    String.contains "ExpectingSymbol" msg |> Expect.equal False |> Expect.onFail msg
            ]
        , describe "semantics"
            [ fuzz2 (O.formula 4) (Fuzz.listOfLengthBetween 0 4 (Fuzz.oneOfValues O.atoms)) "fplValuation agrees with the reference" <|
                \f i -> SS.fplValuation f i |> Expect.equal (O.eval (Set.fromList i) f)
            , fuzz (O.formula 4) "fplSatisfiability" <|
                \f -> SS.fplSatisfiability f |> Expect.equal (O.satisfiable [ f ])
            , fuzz (O.formula 4) "fplUnsatisfiability" <|
                \f -> SS.fplUnsatisfiability f |> Expect.equal (not (O.satisfiable [ f ]))
            , fuzz (O.formula 4) "fplValidity" <|
                \f -> SS.fplValidity f |> Expect.equal (not (O.satisfiable [ Neg f ]))
            , fuzz (O.formula 4) "fplModels are exactly the models over the formula's symbols" <|
                \f -> O.toSet (SS.fplModels f) |> Expect.equal (O.models (O.symbols f) [ f ])
            , fuzz (O.formula 4) "fplCountermodels are exactly the countermodels" <|
                \f -> O.toSet (SS.fplCountermodels f) |> Expect.equal (O.models (O.symbols f) [ Neg f ])
            , fuzz (O.formulaSet 3 3) "splSatisfiability" <|
                \fs -> SS.splSatisfiability fs |> Expect.equal (O.satisfiable fs)
            , fuzz (O.formulaSet 3 3) "splModels" <|
                \fs -> O.toSet (SS.splModels fs) |> Expect.equal (O.models (O.symbolsSet fs) fs)
            , fuzz2 (O.formulaSet 3 3) (O.formula 3) "logicalConsecuence" <|
                \fs g -> SS.logicalConsecuence fs g |> Expect.equal (O.entails fs g)
            , fuzz2 (O.formulaSet 3 3) (O.formula 3) "logicalConsecuence2" <|
                \fs g -> SS.logicalConsecuence2 fs g |> Expect.equal (O.entails fs g)
            , fuzz (O.formula 4) "fplNegation f is equivalent to ¬f" <|
                \f -> O.equivalent (SS.fplNegation f) (Neg f) |> Expect.equal True
            , fuzz (O.formulaSet 3 3) "splConjunction is equivalent to the set" <|
                \fs -> O.clausesEquivalentTo fs [] |> always (O.satisfiable fs == O.satisfiable [ SS.splConjunction fs ]) |> Expect.equal True
            , fuzz (O.formulaSet 3 3) "splConjunction has the same models as the set" <|
                \fs -> O.models (O.symbolsSet fs) [ SS.splConjunction fs ] |> Expect.equal (O.models (O.symbolsSet fs) fs)
            , fuzz (O.formulaSet 3 3) "splDisjunction is the disjunction of the set" <|
                \fs ->
                    O.interpretations (O.symbolsSet fs)
                        |> List.all (\i -> O.eval i (SS.splDisjunction fs) == List.any (O.eval i) fs)
                        |> Expect.equal True
            ]
        ]
