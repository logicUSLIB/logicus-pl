module PLDeductionTests exposing (suite)

{-| Deduction systems: the presets are read, textbook proofs are accepted, each kind of error is rejected, the
steps that the checker accepts are valid (random instances of the rules, checked with truth tables), the hints only
propose correct lines, and a rule has a counterexample exactly when it is not valid.
-}

import Dict exposing (Dict)
import Expect
import Fuzz exposing (Fuzzer)
import List.Extra as LE
import LogicUS.PL.Deduction as D exposing (HintKind(..), Premise(..), Schema(..))
import LogicUS.PL.DeductionSystems as DS
import LogicUS.PL.SyntaxSemantics exposing (FormulaPL(..))
import PLOracle as O
import Set
import Test exposing (Test, describe, fuzz, test)


system : String -> D.System
system txt =
    case D.readSystem txt of
        Ok s ->
            s

        Err _ ->
            []


classical : D.System
classical =
    system DS.naturalDeduction


withDerived : D.System
withDerived =
    system (DS.naturalDeduction ++ "\n" ++ DS.derivedRules)


problem : List String -> String -> D.Problem
problem ps g =
    { premises = List.filterMap (Result.toMaybe << D.readFormula) ps
    , goal = Result.toMaybe (D.readFormula g)
    }


check : D.System -> List String -> String -> String -> D.ProofReport
check sys ps g proof =
    D.checkProof sys (problem ps g) (D.readProof proof)


errorAt : Int -> D.ProofReport -> String
errorAt n rep =
    rep.lines |> LE.find (\l -> l.number == n) |> Maybe.map .message |> Maybe.withDefault "no such line"


type alias Exercise =
    { name : String, sys : D.System, premises : List String, goal : String, proof : String }


exercises : List Exercise
exercises =
    [ { name = "hypothetical syllogism"
      , sys = classical
      , premises = [ "p -> q", "q -> r" ]
      , goal = "p -> r"
      , proof = """
        1 p -> q      premise
        2 q -> r      premise
        3 | p         assumption
        4 | q         ->E 1, 3
        5 | r         ->E 2, 4
        6 p -> r      ->I 3-5"""
      }
    , { name = "commutativity of ∨"
      , sys = classical
      , premises = [ "p | q" ]
      , goal = "q | p"
      , proof = """
        1 p | q       premise
        2 | p         assumption
        3 | q | p     ∨I2 2
        4 | q         assumption
        5 | q | p     ∨I1 4
        6 q | p       ∨E 1, 2-3, 4-5"""
      }
    , { name = "contraposition"
      , sys = classical
      , premises = [ "p -> q" ]
      , goal = "¬q -> ¬p"
      , proof = """
        1 p -> q      premise
        2 | ¬q        assumption
        3 | | p       assumption
        4 | | q       ->E 1, 3
        5 | | !F      ¬E 4, 2
        6 | ¬p        ¬I 3-5
        7 ¬q -> ¬p    ->I 2-6"""
      }
    , { name = "excluded middle (classical)"
      , sys = classical
      , premises = []
      , goal = "p | ¬p"
      , proof = """
        1 | ¬(p | ¬p)     assumption
        2 | | p           assumption
        3 | | p | ¬p      ∨I1 2
        4 | | !F          ¬E 3, 1
        5 | ¬p            ¬I 2-4
        6 | p | ¬p        ∨I2 5
        7 | !F            ¬E 6, 1
        8 p | ¬p          RAA 1-7"""
      }
    , { name = "De Morgan: ¬(p ∨ q) ⊢ ¬p ∧ ¬q"
      , sys = classical
      , premises = [ "¬(p | q)" ]
      , goal = "¬p & ¬q"
      , proof = """
        1 ¬(p | q)    premise
        2 | p         assumption
        3 | p | q     ∨I1 2
        4 | !F        ¬E 3, 1
        5 ¬p          ¬I 2-4
        6 | q         assumption
        7 | p | q     ∨I2 6
        8 | !F        ¬E 7, 1
        9 ¬q          ¬I 6-8
        10 ¬p & ¬q    ∧I 5, 9"""
      }
    , { name = "biconditional"
      , sys = classical
      , premises = [ "p & q" ]
      , goal = "p <-> q"
      , proof = """
        1 p & q       premise
        2 | p         assumption
        3 | q         ∧E2 1
        4 | q         assumption
        5 | p         ∧E1 1
        6 p <-> q     ↔I 2-3, 4-5"""
      }
    , { name = "intuitionistic: p → ¬¬p"
      , sys = system DS.intuitionisticRules
      , premises = []
      , goal = "p -> ¬¬p"
      , proof = """
        1 | p           assumption
        2 | | ¬p        assumption
        3 | | !F        ¬E 1, 2
        4 | ¬¬p         ¬I 2-3
        5 p -> ¬¬p      ->I 1-4"""
      }
    , { name = "derived rules"
      , sys = withDerived
      , premises = [ "p -> q", "¬q", "p | r" ]
      , goal = "r"
      , proof = """
        1 p -> q      premise
        2 ¬q          premise
        3 p | r       premise
        4 ¬p          MT 1, 2
        5 r           DS 3, 4"""
      }
    , { name = "axiomatic: p → p"
      , sys = system DS.axiomatic
      , premises = []
      , goal = "p -> p"
      , proof = """
        1 (p -> ((p -> p) -> p)) -> ((p -> (p -> p)) -> (p -> p))   A2
        2 p -> ((p -> p) -> p)                                       A1
        3 (p -> (p -> p)) -> (p -> p)                                MP 2, 1
        4 p -> (p -> p)                                              A1
        5 p -> p                                                     MP 4, 3"""
      }
    ]


suite : Test
suite =
    describe "deduction"
        [ describe "presets"
            [ test "every preset is read" <|
                \_ ->
                    DS.presets
                        |> List.filterMap
                            (\p ->
                                case D.readSystem p.rules of
                                    Ok _ ->
                                        Nothing

                                    Err e ->
                                        Just (p.name ++ ": " ++ e)
                            )
                        |> Expect.equal []
            , test "every rule of the presets is valid" <|
                \_ ->
                    DS.presets
                        |> List.concatMap (\p -> system p.rules)
                        |> List.filter (\r -> D.ruleCounterexample r /= Nothing)
                        |> List.map .name
                        |> Expect.equal []
            , test "a system is written as it is read" <|
                \_ ->
                    D.readSystem (D.systemToString withDerived) |> Expect.equal (Ok withDerived)
            , test "errors in the rules say the line" <|
                \_ ->
                    D.readSystem "rule ∧I : A, B ⊢ A ∧ B\nrule bad : A, ⊢"
                        |> Expect.equal (Err "line 2: bad: unexpected '⊢'")
            , test "rules of first-order logic are not read" <|
                \_ ->
                    [ "rule ∀E : ∀x A ⊢ A[x/t]", "rule ∃I : A[x/t] ⊢ ∃x A", "axiom =I : t = t", "rule Gen : A ⊢ ∀x A   if x not free in A" ]
                        |> List.map D.readSystem
                        |> Expect.equal
                            [ Err "line 1: ∀E: quantifiers are not propositional (they are for the rules of first-order logic)"
                            , Err "line 1: ∃I: substitutions A[x/t] are not propositional (they are for the rules of first-order logic)"
                            , Err "line 1: =I: equalities are not propositional (they are for the rules of first-order logic)"
                            , Err "line 1: Gen: side conditions (if ...) are not propositional (they are for the rules of first-order logic)"
                            ]
            ]
        , describe "textbook proofs are accepted" <|
            List.map
                (\ex ->
                    test ex.name <|
                        \_ ->
                            check ex.sys ex.premises ex.goal ex.proof
                                |> (\r -> ( r.complete, List.filter (not << .ok) r.lines |> List.map (\l -> String.fromInt l.number ++ ": " ++ l.message) ))
                                |> Expect.equal ( True, [] )
                )
                exercises
        , describe "errors"
            [ test "a rule that does not give the formula" <|
                \_ ->
                    check classical [ "p -> q", "q -> r" ] "p -> r" "p -> q  premise\nq -> r  premise\n| p  assumption\n| r  ->E 1, 3"
                        |> errorAt 4
                        |> Expect.equal "→E (A → B, A ⊢ B) does not give this formula from 1, 3"
            , test "a rule with too many lines" <|
                \_ ->
                    check classical [ "p", "q" ] "p" "p  premise\nq  premise\np  ∧E1 1, 2"
                        |> errorAt 3
                        |> Expect.equal "∧E1 uses 1 premise: A ∧ B"
            , test "a rule that is not in the system" <|
                \_ ->
                    check (system DS.intuitionisticRules) [ "¬¬p" ] "p" "¬¬p  premise\np  ¬¬E 1"
                        |> errorAt 2
                        |> Expect.equal "the rule ¬¬E is not one of the rules of this system"
            , test "a line below" <|
                \_ ->
                    check classical [ "p" ] "p & p" "p  premise\np & p  ∧I 1, 2"
                        |> errorAt 2
                        |> Expect.equal "line 2 can only cite lines above it, not 2"
            , test "a line inside a closed subproof" <|
                \_ ->
                    check classical [] "p -> p" "| p  assumption\np -> p  ->I 1-1\np  R 1"
                        |> errorAt 3
                        |> Expect.equal "line 1 is inside a closed subproof, and cannot be used here"
            , test "a subproof cited by part" <|
                \_ ->
                    check classical [ "q" ] "p -> q" "q  premise\n| p  assumption\n| q  R 1\np -> q  ->I 2-2"
                        |> errorAt 4
                        |> Expect.equal "the subproof that starts at line 2 ends at line 3, not at 2"
            , test "a formula that cannot be read" <|
                \_ ->
                    check classical [ "p" ] "p" "p  premise\np &  R 1"
                        |> errorAt 2
                        |> String.startsWith "the formula cannot be read"
                        |> Expect.equal True
            , test "a premise that is not one of the exercise" <|
                \_ ->
                    check classical [ "p" ] "p" "q  premise"
                        |> errorAt 1
                        |> Expect.equal "this formula is not a premise of the exercise"
            , test "a subproof without assumption" <|
                \_ ->
                    check classical [ "p" ] "p" "p  premise\n| p  R 1"
                        |> errorAt 2
                        |> Expect.equal "this line has more bars than the open subproofs (a subproof starts with an assumption)"
            , test "a proof that ends inside a subproof" <|
                \_ ->
                    check classical [] "p -> p" "| p  assumption"
                        |> .message
                        |> Expect.equal "Every line is correct, but the proof ends inside a subproof."
            , test "a proof that does not end with the goal" <|
                \_ ->
                    check classical [ "p" ] "q" "p  premise"
                        |> .message
                        |> Expect.equal "Every line is correct, but the proof does not end with the goal q."
            ]
        , describe "rules given by the exercise"
            [ test "an exercise can allow only →I and →E" <|
                \_ ->
                    check (system "rule →I : [A] B ⊢ A → B\nrule →E : A → B, A ⊢ B") [ "p -> q", "q -> r" ] "p -> r" (Maybe.withDefault "" (Maybe.map .proof (List.head exercises)))
                        |> .complete
                        |> Expect.equal True
            , test "rules can be added: modus tollens" <|
                \_ ->
                    check (system "rule MT : A → B, ¬B ⊢ ¬A") [ "p -> q", "¬q" ] "¬p" "p -> q  premise\n¬q  premise\n¬p  MT 1, 2"
                        |> .complete
                        |> Expect.equal True
            , test "rule names can be written in ASCII" <|
                \_ ->
                    check classical [ "p", "q" ] "p & q" "p  premise\nq  premise\np & q  &I 1, 2"
                        |> .complete
                        |> Expect.equal True
            , test "a rule that is not valid has a counterexample" <|
                \_ ->
                    system "rule bad : A → B, B ⊢ A\nrule good : A → B, ¬B ⊢ ¬A\naxiom bad2 : A ∨ B"
                        |> List.map D.ruleCounterexample
                        |> Expect.equal [ Just [ ( "A", False ), ( "B", True ) ], Nothing, Just [ ( "A", False ), ( "B", False ) ] ]
            , test "a subproof counts as an implication" <|
                \_ ->
                    system "rule ok : [A] B, [¬A] B ⊢ B\nrule bad : [A] B ⊢ B"
                        |> List.map D.ruleCounterexample
                        |> Expect.equal [ Nothing, Just [ ( "A", False ), ( "B", False ) ] ]
            ]
        , fuzz oneStep "an accepted step is valid (random instances of the rules)" <|
            \( rule, premiseForms, concl ) ->
                if List.all .ok (D.checkProof withDerived { premises = [], goal = Nothing } (stepLines rule premiseForms concl)).lines then
                    O.entails premiseForms concl |> Expect.equal True

                else
                    Expect.pass
        , fuzz correctStep "a correct instance of a rule is accepted" <|
            \( rule, premiseForms, concl ) ->
                D.checkProof withDerived { premises = [], goal = Nothing } (stepLines rule premiseForms concl)
                    |> .lines
                    |> List.filter (not << .ok)
                    |> List.map .message
                    |> Expect.equal []
        , fuzz randomRule "a rule has a counterexample exactly when it is not valid" <|
            \rule ->
                let
                    env =
                        Dict.fromList [ ( "A", Atom ( "p", [] ) ), ( "B", Atom ( "q", [] ) ), ( "C", Atom ( "r", [] ) ) ]

                    hyps =
                        List.map
                            (\p ->
                                case p of
                                    PFormula s ->
                                        inst env s

                                    PSubproof a b ->
                                        Impl (inst env a) (inst env b)
                            )
                            rule.premises

                    valid =
                        O.entails hyps (inst env rule.conclusion)
                in
                case D.ruleCounterexample rule of
                    Nothing ->
                        valid |> Expect.equal True

                    Just v ->
                        let
                            trueAtoms =
                                v
                                    |> List.filter Tuple.second
                                    |> List.filterMap (\( m, _ ) -> Dict.get m env)
                                    |> List.filterMap
                                        (\f ->
                                            case f of
                                                Atom a ->
                                                    Just a

                                                _ ->
                                                    Nothing
                                        )
                                    |> Set.fromList
                        in
                        ( valid, List.all (O.eval trueAtoms) hyps, O.eval trueAtoms (inst env rule.conclusion) )
                            |> Expect.equal ( False, True, False )
        , describe "hints only propose correct lines" <|
            List.map
                (\ex ->
                    test ex.name <|
                        \_ ->
                            let
                                ls =
                                    D.readProof ex.proof

                                prob =
                                    problem ex.premises ex.goal

                                bad =
                                    List.range 0 (List.length ls)
                                        |> List.concatMap
                                            (\k ->
                                                let
                                                    prefix =
                                                        List.take k ls

                                                    openDepth =
                                                        Maybe.withDefault 0 (Maybe.map .depth (LE.last prefix))
                                                in
                                                D.hints ex.sys prob prefix Nothing 30
                                                    |> List.filter (\h -> h.kind /= Backward && h.input /= "")
                                                    |> List.filterMap
                                                        (\h ->
                                                            let
                                                                d =
                                                                    if h.kind == CloseSubproof then
                                                                        openDepth - 1

                                                                    else
                                                                        openDepth

                                                                rep =
                                                                    D.checkProof ex.sys prob (prefix ++ [ { depth = d, formula = h.input, rule = h.rule, refs = h.refs } ])
                                                            in
                                                            case LE.last rep.lines of
                                                                Just l ->
                                                                    if l.ok then
                                                                        Nothing

                                                                    else
                                                                        Just (String.fromInt k ++ ": " ++ h.text ++ " → " ++ l.message)

                                                                Nothing ->
                                                                    Nothing
                                                        )
                                            )
                            in
                            bad |> Expect.equal []
                )
                exercises
        , test "backward hints for the goal" <|
            \_ ->
                D.hints classical (problem [ "p -> q", "q -> r" ] "p -> r") (D.readProof "p -> q  premise\nq -> r  premise") Nothing 10
                    |> List.map .text
                    |> Expect.equal
                        [ "→I gives p → r from a subproof from the assumption p to r"
                        , "RAA gives p → r from a subproof from the assumption ¬ (p → r) to ⊥"
                        ]
        , test "hints when a subproof can be closed" <|
            \_ ->
                D.hints classical (problem [ "p -> q", "q -> r" ] "p -> r") (D.readProof "p -> q  premise\nq -> r  premise\n| p  assumption\n| q  ->E 1, 3\n| r  ->E 2, 4") Nothing 10
                    |> List.filter (\h -> h.kind == CloseSubproof)
                    |> List.map .text
                    |> Expect.equal [ "close the subproof 3-5 and apply →I 3-5: p → r" ]
        , test "the example of the documentation" <|
            \_ ->
                let
                    sys =
                        system "rule →I : [A] B ⊢ A → B\nrule →E : A → B, A ⊢ B"

                    proof =
                        D.readProof "p -> q    premise\nq -> r    premise\n| p    assumption\n| r    ->E 2, 3"

                    exercise =
                        problem [ "p -> q", "q -> r" ] "p -> r"
                in
                ( errorAt 4 (D.checkProof sys exercise proof), (D.checkProof sys exercise proof).complete, List.map .text (D.hints sys exercise proof Nothing 5) )
                    |> Expect.equal ( "→E (A → B, A ⊢ B) does not give this formula from 2, 3", False, [ "→E 1, 3 gives q" ] )
        , test "forward hints from the lines" <|
            \_ ->
                D.hints classical (problem [ "p & q" ] "q & p") (D.readProof "p & q  premise") Nothing 10
                    |> List.filter (\h -> h.kind == Forward)
                    |> List.map .text
                    |> Expect.equal [ "∧E1 1 gives p", "∧E2 1 gives q" ]
        ]



-- RANDOM STEPS


stepLines : D.Rule -> List FormulaPL -> FormulaPL -> List D.ProofLine
stepLines rule premiseForms concl =
    List.map (\f -> { depth = 0, formula = D.formulaToInputString f, rule = "premise", refs = "" }) premiseForms
        ++ [ { depth = 0, formula = D.formulaToInputString concl, rule = rule.name, refs = String.join ", " (List.indexedMap (\i _ -> String.fromInt (i + 1)) premiseForms) } ]



-- the rules without subproofs (with derived rules), instantiated with random formulas


plainRules : List D.Rule
plainRules =
    List.filter (\r -> not (List.isEmpty r.premises) && List.all isFormula r.premises) withDerived


isFormula : Premise -> Bool
isFormula p =
    case p of
        PFormula _ ->
            True

        PSubproof _ _ ->
            False


inst : Dict String FormulaPL -> Schema -> FormulaPL
inst env s =
    case s of
        SMeta a ->
            Maybe.withDefault Taut (Dict.get a env)

        SBot ->
            Insat

        STop ->
            Taut

        SNot a ->
            Neg (inst env a)

        SAnd a b ->
            Conj (inst env a) (inst env b)

        SOr a b ->
            Disj (inst env a) (inst env b)

        SImp a b ->
            Impl (inst env a) (inst env b)

        SIff a b ->
            Equi (inst env a) (inst env b)


ruleInstance : Fuzzer ( D.Rule, Dict String FormulaPL )
ruleInstance =
    Fuzz.map4
        (\r a b c -> ( r, Dict.fromList [ ( "A", a ), ( "B", b ), ( "C", c ) ] ))
        (Fuzz.oneOfValues plainRules)
        (O.formula 2)
        (O.formula 2)
        (O.formula 2)


correctStep : Fuzzer ( D.Rule, List FormulaPL, FormulaPL )
correctStep =
    Fuzz.map
        (\( r, env ) ->
            ( r
            , List.map
                (\p ->
                    case p of
                        PFormula s ->
                            inst env s

                        PSubproof _ _ ->
                            Taut
                )
                r.premises
            , inst env r.conclusion
            )
        )
        ruleInstance



-- a correct instance, or one whose conclusion or premises have been changed


oneStep : Fuzzer ( D.Rule, List FormulaPL, FormulaPL )
oneStep =
    Fuzz.map3
        (\( r, ps, c ) other k ->
            case k of
                0 ->
                    ( r, ps, c )

                1 ->
                    ( r, ps, other )

                2 ->
                    ( r, List.reverse ps, c )

                3 ->
                    ( r
                    , List.map
                        (\p ->
                            if p == c then
                                other

                            else
                                p
                        )
                        ps
                    , Neg c
                    )

                _ ->
                    ( r, other :: List.drop 1 ps, c )
        )
        correctStep
        (O.formula 2)
        (Fuzz.intRange 0 4)



-- random rules over the letters A, B, C


schema : Int -> Fuzzer Schema
schema depth =
    let
        leafS =
            Fuzz.frequency [ ( 6, Fuzz.map SMeta (Fuzz.oneOfValues [ "A", "B", "C" ]) ), ( 1, Fuzz.constant SBot ), ( 1, Fuzz.constant STop ) ]
    in
    if depth <= 0 then
        leafS

    else
        let
            sub =
                Fuzz.lazy (\_ -> schema (depth - 1))
        in
        Fuzz.frequency
            [ ( 2, leafS )
            , ( 1, Fuzz.map SNot sub )
            , ( 1, Fuzz.map2 SAnd sub sub )
            , ( 1, Fuzz.map2 SOr sub sub )
            , ( 1, Fuzz.map2 SImp sub sub )
            , ( 1, Fuzz.map2 SIff sub sub )
            ]


randomRule : Fuzzer D.Rule
randomRule =
    Fuzz.map2 (\ps c -> { name = "r", premises = ps, conclusion = c })
        (Fuzz.listOfLengthBetween 0
            2
            (Fuzz.oneOf [ Fuzz.map PFormula (schema 2), Fuzz.map2 PSubproof (schema 1) (schema 1) ])
        )
        (schema 2)
