module LogicUS.PL.Deduction exposing
    ( Schema(..), Premise(..), Rule, System
    , readSystem, ruleToString, systemToString, findRule, ruleCounterexample
    , readFormula, formulaToString, formulaToInputString
    , ProofLine, Problem, LineReport, ProofReport
    , readProof, proofToString, checkProof
    , Hint, HintKind(..), hints
    )

{-| Deduction systems for propositional logic given by their rules, and proofs checked with them.

A **system** is a list of rules written as schemas, so that each exercise can say which rules may be used:

    rule ∧I : A, B ⊢ A ∧ B
    rule →I : [A] B ⊢ A → B
    rule ∨E : A ∨ B, [A] C, [B] C ⊢ C
    rule RAA : [¬A] ⊥ ⊢ A
    axiom A1 : A → (B → A)

In a schema, a capital letter (`A`, `B`, `C1`...) stands for any formula. A premise `[A] B` is a subproof that
assumes `A` and ends in `B`; the rule closes it. `⊢` can be written `|-`, and the connectives as in the formulas of the
library (`&`, `|`, `->`, `<->`, `¬`, `!F`, `!T`). The systems of `LogicUS.PL.DeductionSystems` are written in this way.

A **proof** is written in the style of Fitch, a line per formula, with bars for the subproofs:

    1  p → q            premise
    2  q → r            premise
    3  | p              assumption
    4  | q              →E 1, 3
    5  | r              →E 2, 4
    6  p → r            →I 3-5

Lines are cited by their number, and closed subproofs by their first and last lines (`3-5`). A line can cite the lines
above it that are not inside a closed subproof. An assumption opens a new subproof; a line with fewer bars closes the
subproofs deeper than it. The line numbers at the beginning are optional (lines are numbered by their position), and
`%` can separate the formula from its justification. `premise` and `assumption` can also be written `premisa`/`P` and
`supuesto`/`A`/`hyp`. The formulas are read with the syntax of `LogicUS.PL.SyntaxSemantics`.

The module also gives **hints**: the rules of the system that can be applied at the end of a proof (to its lines, to
its closed subproofs or closing the current one) and those that would give a target formula.

`LogicUS.FOL.Deduction` (package logicus-fol) extends all this to first-order logic, with the same syntax for rules and
proofs.


# Example

An exercise that only allows the rules of the implication, a proof with one wrong line, and what can be done next:

    import LogicUS.PL.Deduction as D

    rules =
        "rule →I : [A] B ⊢ A → B\nrule →E : A → B, A ⊢ B"

    proof =
        "p -> q    premise\nq -> r    premise\n| p    assumption\n| r    ->E 2, 3"

    exercise =
        { premises = List.filterMap (Result.toMaybe << D.readFormula) [ "p -> q", "q -> r" ]
        , goal = Result.toMaybe (D.readFormula "p -> r")
        }

    case D.readSystem rules of
        Ok sys ->
            ( D.checkProof sys exercise (D.readProof proof)
            , D.hints sys exercise (D.readProof proof) Nothing 5
            )

        Err e ->
            ...

The report says that line 4 is wrong ("→E (A → B, A ⊢ B) does not give this formula from 2, 3") and that the proof
is not complete; among the hints, `→E 1, 3 gives q`. A rule that is not valid, such as `rule bad : A → B, B ⊢ A`, is
still accepted by `readSystem` (an exercise may want to show why it is wrong), and `ruleCounterexample` says why it
is not valid.


# Systems

@docs Schema, Premise, Rule, System
@docs readSystem, ruleToString, systemToString, findRule, ruleCounterexample


# Formulas

@docs readFormula, formulaToString, formulaToInputString


# Proofs

@docs ProofLine, Problem, LineReport, ProofReport
@docs readProof, proofToString, checkProof


# Hints

@docs Hint, HintKind, hints

-}

import Dict exposing (Dict)
import List.Extra as LE
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..))
import Set exposing (Set)



--===========--
--  SYSTEMS  --
--===========--


{-| A formula schema. `SMeta "A"` stands for any formula.
-}
type Schema
    = SMeta String
    | SBot
    | STop
    | SNot Schema
    | SAnd Schema Schema
    | SOr Schema Schema
    | SImp Schema Schema
    | SIff Schema Schema


{-| A premise of a rule: a formula, or a subproof from an assumption to a formula.
-}
type Premise
    = PFormula Schema
    | PSubproof Schema Schema


{-| A rule: its name, its premises and its conclusion. An axiom is a rule without premises.
-}
type alias Rule =
    { name : String
    , premises : List Premise
    , conclusion : Schema
    }


{-| A deduction system: the rules that can be used.
-}
type alias System =
    List Rule



-- READING SCHEMAS


type Token
    = TkIdent String
    | TkSym String


symbols : List ( String, String )
symbols =
    -- longest first; the quantifiers, `/` and `=` are read to say that they are not propositional
    [ ( "<->", "↔" )
    , ( "|-", "⊢" )
    , ( "->", "→" )
    , ( "!A", "∀" )
    , ( "!E", "∃" )
    , ( "!F", "⊥" )
    , ( "!T", "⊤" )
    , ( "_|_", "⊥" )
    , ( "↔", "↔" )
    , ( "→", "→" )
    , ( "⊢", "⊢" )
    , ( "∧", "∧" )
    , ( "&", "∧" )
    , ( "∨", "∨" )
    , ( "|", "∨" )
    , ( "¬", "¬" )
    , ( "~", "¬" )
    , ( "-", "¬" )
    , ( "∀", "∀" )
    , ( "∃", "∃" )
    , ( "⊥", "⊥" )
    , ( "⊤", "⊤" )
    , ( "(", "(" )
    , ( ")", ")" )
    , ( "[", "[" )
    , ( "]", "]" )
    , ( "/", "/" )
    , ( ",", "," )
    , ( "=", "=" )
    ]


tokenize : String -> Result String (List Token)
tokenize src =
    let
        isIdentChar c =
            Char.isAlphaNum c || c == '_' || c == '\''

        go s acc =
            case String.uncons s of
                Nothing ->
                    Ok (List.reverse acc)

                Just ( c, rest ) ->
                    if c == ' ' || c == '\t' then
                        go rest acc

                    else if Char.isAlpha c then
                        let
                            name =
                                String.fromChar c ++ takeWhile isIdentChar rest
                        in
                        go (String.dropLeft (String.length name) s) (TkIdent name :: acc)

                    else
                        case LE.find (\( sym, _ ) -> String.startsWith sym s) symbols of
                            Just ( sym, canon ) ->
                                go (String.dropLeft (String.length sym) s) (TkSym canon :: acc)

                            Nothing ->
                                Err ("unexpected symbol '" ++ String.fromChar c ++ "'")
    in
    go src []


takeWhile : (Char -> Bool) -> String -> String
takeWhile p s =
    case String.uncons s of
        Just ( c, rest ) ->
            if p c then
                String.cons c (takeWhile p rest)

            else
                ""

        Nothing ->
            ""


isFormulaMeta : String -> Bool
isFormulaMeta name =
    case String.uncons name of
        Just ( c, _ ) ->
            Char.isUpper c

        Nothing ->
            False


firstOrder : String -> String
firstOrder what =
    what ++ " are not propositional (they are for the rules of first-order logic)"



-- Recursive descent: iff < imp (right) < or < and < unary. Each function returns the rest of the tokens.


type alias P a =
    List Token -> Result String ( a, List Token )


parseSchema : P Schema
parseSchema ts =
    parseIff ts


parseIff : P Schema
parseIff ts =
    parseImp ts
        |> Result.andThen
            (\( l, rest ) ->
                case rest of
                    (TkSym "↔") :: rest2 ->
                        parseIff rest2 |> Result.map (\( r, rest3 ) -> ( SIff l r, rest3 ))

                    _ ->
                        Ok ( l, rest )
            )


parseImp : P Schema
parseImp ts =
    parseOr ts
        |> Result.andThen
            (\( l, rest ) ->
                case rest of
                    (TkSym "→") :: rest2 ->
                        parseImp rest2 |> Result.map (\( r, rest3 ) -> ( SImp l r, rest3 ))

                    _ ->
                        Ok ( l, rest )
            )


parseOr : P Schema
parseOr ts =
    let
        loop l rest =
            case rest of
                (TkSym "∨") :: rest2 ->
                    parseAnd rest2 |> Result.andThen (\( r, rest3 ) -> loop (SOr l r) rest3)

                _ ->
                    Ok ( l, rest )
    in
    parseAnd ts |> Result.andThen (\( l, rest ) -> loop l rest)


parseAnd : P Schema
parseAnd ts =
    let
        loop l rest =
            case rest of
                (TkSym "∧") :: rest2 ->
                    parseUnary rest2 |> Result.andThen (\( r, rest3 ) -> loop (SAnd l r) rest3)

                _ ->
                    Ok ( l, rest )
    in
    parseUnary ts |> Result.andThen (\( l, rest ) -> loop l rest)


parseUnary : P Schema
parseUnary ts =
    case ts of
        (TkSym "¬") :: rest ->
            parseUnary rest |> Result.map (\( s, rest2 ) -> ( SNot s, rest2 ))

        (TkSym "∀") :: _ ->
            Err (firstOrder "quantifiers")

        (TkSym "∃") :: _ ->
            Err (firstOrder "quantifiers")

        _ ->
            parsePrimary ts
                |> Result.andThen
                    (\( s, rest ) ->
                        case rest of
                            (TkSym "[") :: (TkIdent _) :: (TkSym "/") :: _ ->
                                Err (firstOrder "substitutions A[x/t]")

                            _ ->
                                Ok ( s, rest )
                    )


parsePrimary : P Schema
parsePrimary ts =
    case ts of
        (TkSym "(") :: rest ->
            parseSchema rest
                |> Result.andThen
                    (\( s, rest2 ) ->
                        case rest2 of
                            (TkSym ")") :: rest3 ->
                                Ok ( s, rest3 )

                            _ ->
                                Err "expected ')'"
                    )

        (TkSym "⊥") :: rest ->
            Ok ( SBot, rest )

        (TkSym "⊤") :: rest ->
            Ok ( STop, rest )

        (TkIdent _) :: (TkSym "=") :: _ ->
            Err (firstOrder "equalities")

        (TkIdent a) :: rest ->
            if isFormulaMeta a then
                Ok ( SMeta a, rest )

            else
                Err ("'" ++ a ++ "' is not a formula (formulas are written with capital letters: A, B...)")

        (TkSym s) :: _ ->
            Err ("unexpected '" ++ s ++ "'")

        [] ->
            Err "the schema is incomplete"


parsePremises : P (List Premise)
parsePremises ts =
    let
        one tks =
            case tks of
                (TkSym "[") :: rest ->
                    parseSchema rest
                        |> Result.andThen
                            (\( a, rest2 ) ->
                                case rest2 of
                                    (TkSym "]") :: rest3 ->
                                        parseSchema rest3 |> Result.map (\( c, rest4 ) -> ( PSubproof a c, rest4 ))

                                    _ ->
                                        Err "expected ']' after the assumption"
                            )

                _ ->
                    parseSchema tks |> Result.map (\( s, rest ) -> ( PFormula s, rest ))

        loop acc tks =
            one tks
                |> Result.andThen
                    (\( p, rest ) ->
                        case rest of
                            (TkSym ",") :: rest2 ->
                                loop (p :: acc) rest2

                            _ ->
                                Ok ( List.reverse (p :: acc), rest )
                    )
    in
    case ts of
        (TkSym "⊢") :: _ ->
            Ok ( [], ts )

        _ ->
            loop [] ts


readRule : String -> Result String Rule
readRule line =
    let
        body =
            String.trim <|
                if String.startsWith "rule " line then
                    String.dropLeft 5 line

                else if String.startsWith "axiom " line then
                    String.dropLeft 6 line

                else
                    line

        ( name, rest ) =
            case String.indexes ":" body of
                i :: _ ->
                    ( String.trim (String.left i body), String.dropLeft (i + 1) body )

                [] ->
                    ( "", body )

        withTurnstile =
            if String.contains "⊢" rest || String.contains "|-" rest then
                rest

            else
                "⊢ " ++ rest
    in
    if name == "" || String.contains " " name then
        Err "a rule is written 'rule NAME : premises ⊢ conclusion' (the name without spaces)"

    else if String.contains " if " rest then
        Err (name ++ ": " ++ firstOrder "side conditions (if ...)")

    else
        tokenize withTurnstile
            |> Result.andThen parsePremises
            |> Result.andThen
                (\( ps, rest2 ) ->
                    case rest2 of
                        (TkSym "⊢") :: rest3 ->
                            parseSchema rest3
                                |> Result.andThen
                                    (\( c, rest4 ) ->
                                        if List.isEmpty rest4 then
                                            Ok { name = name, premises = ps, conclusion = c }

                                        else
                                            Err "unexpected text after the conclusion"
                                    )

                        _ ->
                            Err "expected '⊢' between the premises and the conclusion"
                )
            |> Result.mapError (\e -> name ++ ": " ++ e)


{-| It reads a system: a rule per line (`rule NAME : premises ⊢ conclusion`, or `axiom NAME : formula`). Empty lines
and lines starting with `#` or `--` are ignored. The errors say the line.

    readSystem "rule →E : A → B, A ⊢ B"
        == Ok [ { name = "→E", premises = [ PFormula (SImp (SMeta "A") (SMeta "B")), PFormula (SMeta "A") ], conclusion = SMeta "B" } ]

-}
readSystem : String -> Result String System
readSystem src =
    src
        |> String.lines
        |> List.indexedMap Tuple.pair
        |> List.filter (\( _, l ) -> not (String.isEmpty (String.trim l) || String.startsWith "#" (String.trim l) || String.startsWith "--" (String.trim l)))
        |> List.foldr
            (\( i, l ) acc ->
                case ( readRule (String.trim l), acc ) of
                    ( Ok r, Ok rs ) ->
                        Ok (r :: rs)

                    ( Err e, _ ) ->
                        Err ("line " ++ String.fromInt (i + 1) ++ ": " ++ e)

                    ( _, Err e ) ->
                        Err e
            )
            (Ok [])



-- WRITING SCHEMAS


schemaToString : Schema -> String
schemaToString s =
    let
        prec x =
            case x of
                SIff _ _ ->
                    1

                SImp _ _ ->
                    2

                SOr _ _ ->
                    3

                SAnd _ _ ->
                    4

                _ ->
                    5

        par p x =
            if prec x < p then
                "(" ++ schemaToString x ++ ")"

            else
                schemaToString x
    in
    case s of
        SMeta a ->
            a

        SBot ->
            "⊥"

        STop ->
            "⊤"

        SNot a ->
            "¬" ++ par 5 a

        SAnd a b ->
            par 4 a ++ " ∧ " ++ par 5 b

        SOr a b ->
            par 3 a ++ " ∨ " ++ par 4 b

        SImp a b ->
            par 3 a ++ " → " ++ par 2 b

        SIff a b ->
            par 2 a ++ " ↔ " ++ par 1 b


premiseToString : Premise -> String
premiseToString p =
    case p of
        PFormula s ->
            schemaToString s

        PSubproof a b ->
            "[" ++ schemaToString a ++ "] " ++ schemaToString b


{-| It writes a rule as `readSystem` reads it.

    ruleToString { name = "→I", premises = [ PSubproof (SMeta "A") (SMeta "B") ], conclusion = SImp (SMeta "A") (SMeta "B") }
        == "rule →I : [A] B ⊢ A → B"

-}
ruleToString : Rule -> String
ruleToString r =
    if List.isEmpty r.premises then
        "axiom " ++ r.name ++ " : " ++ schemaToString r.conclusion

    else
        "rule " ++ r.name ++ " : " ++ String.join ", " (List.map premiseToString r.premises) ++ " ⊢ " ++ schemaToString r.conclusion


{-| It writes a system as `readSystem` reads it.
-}
systemToString : System -> String
systemToString sys =
    String.join "\n" (List.map ruleToString sys)


normalizeName : String -> String
normalizeName n =
    n
        |> String.replace "<->" "↔"
        |> String.replace "->" "→"
        |> String.replace "&" "∧"
        |> String.replace "\\/" "∨"
        |> String.replace "~" "¬"
        |> String.replace "_|_" "⊥"
        |> String.toLower


{-| It finds a rule of a system by its name. The name can use the ASCII forms of the connectives (`->I` for `→I`),
and upper and lower case are not distinguished.
-}
findRule : System -> String -> Maybe Rule
findRule sys name =
    LE.find (\r -> normalizeName r.name == normalizeName name) sys


{-| A valuation of the letters of a rule under which its premises are true and its conclusion is false (a subproof
`[A] B` counts as `A → B`), if there is one. There is none exactly when the rule is valid in classical logic: then
every step made with it goes from true lines to a true line. Rules that are only valid classically (`¬¬E`, `RAA`)
have no counterexample, even in an intuitionistic system.

    -- rule bad : A → B, B ⊢ A
    ruleCounterexample bad == Just [ ( "A", False ), ( "B", True ) ]

-}
ruleCounterexample : Rule -> Maybe (List ( String, Bool ))
ruleCounterexample rule =
    let
        hyps =
            List.map
                (\p ->
                    case p of
                        PFormula s ->
                            s

                        PSubproof a b ->
                            SImp a b
                )
                rule.premises

        metas =
            Set.toList (List.foldl (\s acc -> Set.union acc (schemaMetas s)) (schemaMetas rule.conclusion) hyps)

        valuations ms =
            case ms of
                [] ->
                    [ [] ]

                m :: more ->
                    let
                        rest =
                            valuations more
                    in
                    List.map ((::) ( m, True )) rest ++ List.map ((::) ( m, False )) rest

        holds v s =
            evalSchema (Dict.fromList v) s
    in
    LE.find (\v -> List.all (holds v) hyps && not (holds v rule.conclusion)) (valuations metas)


evalSchema : Dict String Bool -> Schema -> Bool
evalSchema v s =
    case s of
        SMeta a ->
            Maybe.withDefault False (Dict.get a v)

        SBot ->
            False

        STop ->
            True

        SNot a ->
            not (evalSchema v a)

        SAnd a b ->
            evalSchema v a && evalSchema v b

        SOr a b ->
            evalSchema v a || evalSchema v b

        SImp a b ->
            not (evalSchema v a) || evalSchema v b

        SIff a b ->
            evalSchema v a == evalSchema v b



--============--
--  FORMULAS  --
--============--


{-| It reads a formula in the syntax of `LogicUS.PL.SyntaxSemantics` (`p -> q`, `¬p & q_{1}`, `!F`).
-}
readFormula : String -> Result String FormulaPL
readFormula s =
    case PL_SS.fplReadFromString s of
        ( Just f, _, _ ) ->
            Ok f

        ( Nothing, _, e ) ->
            Err ("the formula cannot be read (" ++ e ++ ")")


{-| It writes a formula (with `fplToString`).
-}
formulaToString : FormulaPL -> String
formulaToString =
    PL_SS.fplToString


{-| It writes a formula in the syntax that `readFormula` reads.
-}
formulaToInputString : FormulaPL -> String
formulaToInputString =
    PL_SS.fplToInputString



--============--
--  MATCHING  --
--============--


type alias Env =
    Dict String FormulaPL


matchS : Schema -> FormulaPL -> Env -> Maybe Env
matchS s f env =
    let
        both a b x y =
            matchS a x env |> Maybe.andThen (matchS b y)
    in
    case ( s, f ) of
        ( SMeta a, _ ) ->
            case Dict.get a env of
                Just g ->
                    if g == f then
                        Just env

                    else
                        Nothing

                Nothing ->
                    Just (Dict.insert a f env)

        ( SBot, Insat ) ->
            Just env

        ( STop, Taut ) ->
            Just env

        ( SNot a, Neg x ) ->
            matchS a x env

        ( SAnd a b, Conj x y ) ->
            both a b x y

        ( SOr a b, Disj x y ) ->
            both a b x y

        ( SImp a b, Impl x y ) ->
            both a b x y

        ( SIff a b, Equi x y ) ->
            both a b x y

        _ ->
            Nothing



-- The formula of a schema whose letters are all known.


instantiate : Env -> Schema -> Maybe FormulaPL
instantiate env s =
    let
        two c a b =
            Maybe.map2 c (instantiate env a) (instantiate env b)
    in
    case s of
        SMeta a ->
            Dict.get a env

        SBot ->
            Just Insat

        STop ->
            Just Taut

        SNot a ->
            Maybe.map Neg (instantiate env a)

        SAnd a b ->
            two Conj a b

        SOr a b ->
            two Disj a b

        SImp a b ->
            two Impl a b

        SIff a b ->
            two Equi a b



-- Matching of a rule: the formula premises with lines, the subproofs with (assumption, end) and the conclusion.


type Item
    = ILine Int FormulaPL
    | IBox Int Int FormulaPL FormulaPL


matchPremise : Premise -> Item -> Env -> Maybe Env
matchPremise p item env =
    case ( p, item ) of
        ( PFormula s, ILine _ f ) ->
            matchS s f env

        ( PSubproof a c, IBox _ _ fa fc ) ->
            matchS a fa env |> Maybe.andThen (matchS c fc)

        _ ->
            Nothing



-- The ways of matching the cited items with the premises (in any order), with the conclusion.


matchRule : Rule -> List Item -> Maybe FormulaPL -> List Env
matchRule rule items concl =
    let
        start =
            case concl of
                Just f ->
                    matchS rule.conclusion f Dict.empty

                Nothing ->
                    Just Dict.empty

        assign ps its env =
            case ps of
                [] ->
                    if List.isEmpty its then
                        [ env ]

                    else
                        []

                p :: more ->
                    its
                        |> LE.select
                        |> List.concatMap
                            (\( it, others ) ->
                                case matchPremise p it env of
                                    Just env2 ->
                                        assign more others env2

                                    Nothing ->
                                        []
                            )
    in
    case start of
        Just env ->
            assign rule.premises items env

        Nothing ->
            []



--==========--
--  PROOFS  --
--==========--


{-| A line of a proof: its depth (the number of open subproofs it is in), its formula, its rule (`premise`,
`assumption` or the name of a rule) and the lines it cites (`"1, 3"`, `"3-5"`).
-}
type alias ProofLine =
    { depth : Int
    , formula : String
    , rule : String
    , refs : String
    }


{-| An exercise: its premises and the formula to prove (if any).
-}
type alias Problem =
    { premises : List FormulaPL
    , goal : Maybe FormulaPL
    }


{-| The verdict on a line: its number, its formula (if it could be read) and whether it is correct, with an
explanation.
-}
type alias LineReport =
    { number : Int
    , formula : Maybe FormulaPL
    , ok : Bool
    , message : String
    }


{-| The verdict on a proof: a report per line, whether the proof is complete (every line is correct and the last one
is the goal, out of every subproof) and a sentence that sums it up.
-}
type alias ProofReport =
    { lines : List LineReport
    , complete : Bool
    , message : String
    }


isPremiseWord : String -> Bool
isPremiseWord w =
    List.member (String.toLower w) [ "premise", "premisa", "p", "pr", "prem" ]


isAssumptionWord : String -> Bool
isAssumptionWord w =
    List.member (String.toLower w) [ "assumption", "supuesto", "a", "hyp", "hip", "hipótesis", "hipotesis", "sup" ]


isRefToken : String -> Bool
isRefToken w =
    not (String.isEmpty w) && String.all (\c -> Char.isDigit c || c == ',' || c == '-' || c == '–') w


{-| It reads a proof written as text, a line per formula (see the beginning of the module).

    readProof "1  p → q   premise\n2  | p   assumption\n3  | q   →E 1, 2"
        == [ { depth = 0, formula = "p → q", rule = "premise", refs = "" }
           , { depth = 1, formula = "p", rule = "assumption", refs = "" }
           , { depth = 1, formula = "q", rule = "→E", refs = "1, 2" }
           ]

-}
readProof : String -> List ProofLine
readProof src =
    let
        line l =
            let
                -- optional line number
                noNumber =
                    case String.words l of
                        w :: _ ->
                            let
                                w2 =
                                    if String.endsWith "." w then
                                        String.dropRight 1 w

                                    else
                                        w
                            in
                            if String.all Char.isDigit w2 && not (String.isEmpty w2) then
                                String.dropLeft (String.length w) (String.trimLeft l)

                            else
                                l

                        [] ->
                            l

                ( depth, rest ) =
                    countBars (String.trimLeft noNumber) 0

                ( formula, just ) =
                    case String.indexes "%" rest of
                        i :: _ ->
                            ( String.trim (String.left i rest), String.words (String.dropLeft (i + 1) rest) )

                        [] ->
                            splitJustification (String.words rest)

                ( rule, refs ) =
                    case just of
                        r :: more ->
                            ( r, String.join " " more )

                        [] ->
                            ( "", "" )
            in
            { depth = depth, formula = formula, rule = rule, refs = refs }
    in
    src
        |> String.lines
        |> List.filter (not << String.isEmpty << String.trim)
        |> List.map line


countBars : String -> Int -> ( Int, String )
countBars s n =
    case String.uncons s of
        Just ( '|', rest ) ->
            countBars (String.trimLeft rest) (n + 1)

        Just ( '│', rest ) ->
            countBars (String.trimLeft rest) (n + 1)

        _ ->
            ( n, s )



-- The justification is at the end: a word (premise, assumption, or the name of a rule) followed by references.


splitJustification : List String -> ( String, List String )
splitJustification ws =
    let
        rev =
            List.reverse ws

        refs =
            LE.takeWhile isRefToken rev

        afterRefs =
            List.drop (List.length refs) rev
    in
    case afterRefs of
        name :: formulaRev ->
            ( String.join " " (List.reverse formulaRev), name :: List.reverse refs )

        [] ->
            ( String.join " " ws, [] )


{-| It writes a proof as text, with its line numbers and bars.
-}
proofToString : List ProofLine -> String
proofToString ls =
    let
        rows =
            List.indexedMap
                (\i l ->
                    ( String.padLeft 3 ' ' (String.fromInt (i + 1)) ++ "  " ++ String.repeat l.depth "| " ++ l.formula
                    , String.trim (l.rule ++ " " ++ l.refs)
                    )
                )
                ls

        width =
            Maybe.withDefault 0 (List.maximum (List.map (String.length << Tuple.first) rows))
    in
    String.join "\n" (List.map (\( a, b ) -> String.padRight (width + 4) ' ' a ++ b) rows)


type Ref
    = RLine Int
    | RRange Int Int


readRefs : String -> Result String (List Ref)
readRefs s =
    s
        |> String.replace "–" "-"
        |> String.replace " " ","
        |> String.split ","
        |> List.filter (not << String.isEmpty)
        |> List.foldr
            (\part acc ->
                case ( String.split "-" part, acc ) of
                    ( [ a ], Ok rs ) ->
                        case String.toInt a of
                            Just n ->
                                Ok (RLine n :: rs)

                            Nothing ->
                                Err ("'" ++ part ++ "' is not a line number")

                    ( [ a, b ], Ok rs ) ->
                        case ( String.toInt a, String.toInt b ) of
                            ( Just n, Just m ) ->
                                Ok (RRange n m :: rs)

                            _ ->
                                Err ("'" ++ part ++ "' is not a range of lines")

                    ( _, Err e ) ->
                        Err e

                    _ ->
                        Err ("'" ++ part ++ "' is not a line number")
            )
            (Ok [])



-- The structure of a proof: for each line, the subproofs it is in (their first lines, outermost first); for each
-- subproof, its last line.


type alias Structure =
    { paths : Dict Int (List Int)
    , ends : Dict Int Int
    , errors : Dict Int String
    , openAtEnd : List Int
    }


type Just
    = JPremise
    | JAssumption
    | JRule String


justification : ProofLine -> Just
justification l =
    if isPremiseWord l.rule && String.isEmpty (String.trim l.refs) then
        JPremise

    else if isAssumptionWord l.rule && String.isEmpty (String.trim l.refs) then
        JAssumption

    else
        JRule l.rule


structure : List ProofLine -> Structure
structure ls =
    let
        step ( n, l ) ( st, stack ) =
            let
                closeTo d stk acc =
                    if List.length stk > d then
                        case stk of
                            b :: more ->
                                closeTo d more { acc | ends = Dict.insert b (n - 1) acc.ends }

                            [] ->
                                ( stk, acc )

                    else
                        ( stk, acc )

                current =
                    List.length stack
            in
            case justification l of
                JAssumption ->
                    if l.depth < 1 || l.depth > current + 1 then
                        ( { st | errors = Dict.insert n "an assumption opens a subproof: it has one bar more than the line it follows, or as many as a subproof that ends before it" st.errors, paths = Dict.insert n (List.reverse stack) st.paths }, stack )

                    else
                        let
                            ( stk, st2 ) =
                                closeTo (l.depth - 1) stack st
                        in
                        ( { st2 | paths = Dict.insert n (List.reverse (n :: stk)) st2.paths }, n :: stk )

                _ ->
                    if l.depth > current then
                        ( { st | errors = Dict.insert n "this line has more bars than the open subproofs (a subproof starts with an assumption)" st.errors, paths = Dict.insert n (List.reverse stack) st.paths }, stack )

                    else
                        let
                            ( stk, st2 ) =
                                closeTo l.depth stack st
                        in
                        ( { st2 | paths = Dict.insert n (List.reverse stk) st2.paths }, stk )

        ( final, openStack ) =
            List.foldl step ( { paths = Dict.empty, ends = Dict.empty, errors = Dict.empty, openAtEnd = [] }, [] ) (List.indexedMap (\i l -> ( i + 1, l )) ls)

        lastN =
            List.length ls
    in
    { final | ends = List.foldl (\b acc -> Dict.insert b lastN acc) final.ends openStack, openAtEnd = openStack }


isPrefix : List a -> List a -> Bool
isPrefix xs ys =
    List.take (List.length xs) ys == xs


parentPath : Structure -> Int -> List Int
parentPath st b =
    List.reverse (List.drop 1 (List.reverse (Maybe.withDefault [] (Dict.get b st.paths))))



-- The lines and closed subproofs that the line n can cite (lines before it out of closed subproofs).


accessible : Structure -> Dict Int FormulaPL -> Int -> List Int -> List Item
accessible st forms n path =
    let
        lines =
            List.range 1 (n - 1)
                |> List.filter (\i -> isPrefix (Maybe.withDefault [] (Dict.get i st.paths)) path)

        boxes =
            Dict.toList st.ends
                |> List.filter (\( b, e ) -> e < n && isPrefix (parentPath st b) path)

        lineItems =
            List.filterMap (\i -> Maybe.map (ILine i) (Dict.get i forms)) lines

        boxItems =
            List.filterMap (\( b, e ) -> Maybe.map2 (IBox b e) (Dict.get b forms) (Dict.get e forms)) boxes
    in
    lineItems ++ boxItems


refToItem : Structure -> Dict Int FormulaPL -> Int -> List Int -> Ref -> Result String Item
refToItem st forms n path ref =
    case ref of
        RLine i ->
            if i >= n || i < 1 then
                Err ("line " ++ String.fromInt n ++ " can only cite lines above it, not " ++ String.fromInt i)

            else if not (isPrefix (Maybe.withDefault [] (Dict.get i st.paths)) path) then
                Err ("line " ++ String.fromInt i ++ " is inside a closed subproof, and cannot be used here")

            else
                case Dict.get i forms of
                    Just f ->
                        Ok (ILine i f)

                    Nothing ->
                        Err ("line " ++ String.fromInt i ++ " cannot be read")

        RRange a b ->
            case Dict.get a st.ends of
                Nothing ->
                    Err ("line " ++ String.fromInt a ++ " does not open a subproof (an assumption does)")

                Just e ->
                    if e /= b then
                        Err ("the subproof that starts at line " ++ String.fromInt a ++ " ends at line " ++ String.fromInt e ++ ", not at " ++ String.fromInt b)

                    else if e >= n then
                        Err ("the subproof " ++ String.fromInt a ++ "-" ++ String.fromInt b ++ " is not closed before line " ++ String.fromInt n)

                    else if not (isPrefix (parentPath st a) path) then
                        Err ("the subproof " ++ String.fromInt a ++ "-" ++ String.fromInt b ++ " is inside a closed subproof, and cannot be used here")

                    else
                        case ( Dict.get a forms, Dict.get b forms ) of
                            ( Just fa, Just fb ) ->
                                Ok (IBox a b fa fb)

                            _ ->
                                Err ("the subproof " ++ String.fromInt a ++ "-" ++ String.fromInt b ++ " has lines that cannot be read")


{-| It checks a proof with the rules of a system. The premises of the proof must be premises of the problem (if it
has any), and the proof is complete when it ends with the goal.

    checkProof sys { premises = [ p → q, q → r ], goal = Just (p → r) } (readProof proof)

-}
checkProof : System -> Problem -> List ProofLine -> ProofReport
checkProof sys problem ls =
    let
        numbered =
            List.indexedMap (\i l -> ( i + 1, l )) ls

        parsed =
            Dict.fromList (List.map (\( n, l ) -> ( n, readFormula l.formula )) numbered)

        forms =
            Dict.foldl
                (\n r acc ->
                    case r of
                        Ok f ->
                            Dict.insert n f acc

                        Err _ ->
                            acc
                )
                Dict.empty
                parsed

        st =
            structure ls

        checkLine ( n, l ) =
            let
                path =
                    Maybe.withDefault [] (Dict.get n st.paths)

                report ok msg =
                    { number = n, formula = Dict.get n forms, ok = ok, message = msg }
            in
            case ( Maybe.withDefault (Err "") (Dict.get n parsed), Dict.get n st.errors ) of
                ( Err e, _ ) ->
                    report False e

                ( _, Just e ) ->
                    report False e

                ( Ok f, Nothing ) ->
                    case justification l of
                        JPremise ->
                            if l.depth /= 0 then
                                report False "a premise cannot be inside a subproof"

                            else if not (List.isEmpty problem.premises) && not (List.member f problem.premises) then
                                report False "this formula is not a premise of the exercise"

                            else
                                report True "premise"

                        JAssumption ->
                            report True "assumption"

                        JRule name ->
                            if String.isEmpty name then
                                report False "the line needs a justification: premise, assumption, or a rule and the lines it uses"

                            else
                                case findRule sys name of
                                    Nothing ->
                                        report False ("the rule " ++ name ++ " is not one of the rules of this system")

                                    Just rule ->
                                        case readRefs l.refs |> Result.andThen (collect << List.map (refToItem st forms n path)) of
                                            Err e ->
                                                report False e

                                            Ok items ->
                                                checkStep rule items f report

        lineReports =
            List.map checkLine numbered

        lastOk =
            case List.reverse numbered of
                ( n, l ) :: _ ->
                    if l.depth /= 0 || not (List.isEmpty st.openAtEnd) then
                        Err "the proof ends inside a subproof"

                    else
                        case problem.goal of
                            Just g ->
                                if Dict.get n forms == Just g then
                                    Ok ()

                                else
                                    Err ("the proof does not end with the goal " ++ formulaToString g)

                            Nothing ->
                                Ok ()

                [] ->
                    Err "the proof is empty"

        allOk =
            List.all .ok lineReports

        message =
            case ( allOk, lastOk ) of
                ( True, Ok () ) ->
                    "The proof is correct and complete."

                ( True, Err e ) ->
                    "Every line is correct, but " ++ e ++ "."

                ( False, _ ) ->
                    "Wrong lines: " ++ String.join ", " (List.map (String.fromInt << .number) (List.filter (not << .ok) lineReports)) ++ "."
    in
    { lines = lineReports, complete = allOk && lastOk == Ok (), message = message }


collect : List (Result String a) -> Result String (List a)
collect rs =
    List.foldr (Result.map2 (::)) (Ok []) rs


checkStep : Rule -> List Item -> FormulaPL -> (Bool -> String -> LineReport) -> LineReport
checkStep rule items f report =
    if List.length items /= List.length rule.premises then
        report False
            (rule.name
                ++ " uses "
                ++ String.fromInt (List.length rule.premises)
                ++ (if List.length rule.premises == 1 then
                        " premise"

                    else
                        " premises"
                   )
                ++ (if List.isEmpty rule.premises then
                        ""

                    else
                        ": " ++ String.join ", " (List.map premiseToString rule.premises)
                   )
            )

    else if List.isEmpty (matchRule rule items (Just f)) then
        report False (rule.name ++ " (" ++ ruleShape rule ++ ") does not give this formula from " ++ String.join ", " (List.map itemRef items))

    else
        report True rule.name


ruleShape : Rule -> String
ruleShape rule =
    String.join ", " (List.map premiseToString rule.premises) ++ " ⊢ " ++ schemaToString rule.conclusion


itemRef : Item -> String
itemRef it =
    case it of
        ILine n _ ->
            String.fromInt n

        IBox a b _ _ ->
            String.fromInt a ++ "-" ++ String.fromInt b



--=========--
--  HINTS  --
--=========--


{-| The kind of a hint: a rule applied to the accessible lines and subproofs, a rule that closes the current
subproof, or a rule that would give the target.
-}
type HintKind
    = Forward
    | CloseSubproof
    | Backward


{-| A hint: the rule, the lines it uses (`refs`), the formula it gives (`result`), the same formula in the syntax of
the proofs (`input`), for backward hints what is still needed (unknown parts are written `?A`) and the assumptions of
the subproofs it needs (in the syntax of the proofs, when they are known), and a sentence that explains it.
-}
type alias Hint =
    { kind : HintKind
    , rule : String
    , refs : String
    , result : String
    , input : String
    , needs : List String
    , assumptions : List String
    , text : String
    }



-- A schema with its unknown letters written as placeholders ?A.


partialToString : Env -> Schema -> String
partialToString env s =
    let
        withPlaceholders =
            Set.foldl
                (\a e ->
                    if Dict.member a e then
                        e

                    else
                        Dict.insert a (Atom ( "?" ++ a, [] )) e
                )
                env
                (schemaMetas s)
    in
    case instantiate withPlaceholders s of
        Just f ->
            formulaToString f

        Nothing ->
            schemaToString s


{-| The rules of the system that can be used at the end of a proof:

  - `CloseSubproof`: a rule that closes the subproof that is open at the end, using it;
  - `Backward`: a rule whose conclusion is the target (or the goal of the problem, when no subproof is open), with
    what it still needs; the parts of the premises that are lines of the proof are taken from them;
  - `Forward`: a rule whose premises are lines and closed subproofs that can be cited there, when its result is
    useful: part of the target or of a cited line, or ⊥.

Only the correct lines are used. Rules that only copy a line, and results that are already lines that can be cited,
are left out. At most `limit` hints of each kind are given.

-}
hints : System -> Problem -> List ProofLine -> Maybe FormulaPL -> Int -> List Hint
hints sys problem ls target limit =
    let
        n =
            List.length ls + 1

        -- only the correct lines can be used
        forms =
            (checkProof sys problem ls).lines
                |> List.filterMap
                    (\r ->
                        if r.ok then
                            Maybe.map (Tuple.pair r.number) r.formula

                        else
                            Nothing
                    )
                |> Dict.fromList

        st =
            structure ls

        path =
            List.reverse st.openAtEnd

        items =
            accessible st forms n path

        available =
            List.filterMap
                (\it ->
                    case it of
                        ILine _ f ->
                            Just f

                        _ ->
                            Nothing
                )
                items

        goal =
            case target of
                Just t ->
                    Just t

                Nothing ->
                    if List.isEmpty path then
                        problem.goal

                    else
                        Nothing

        goalParts =
            Maybe.withDefault [] (Maybe.map subformulas goal)

        useful rule =
            not (List.length rule.premises == 1 && rule.premises == [ PFormula rule.conclusion ])

        refsOf chosen =
            String.join ", " (List.map itemRef chosen)

        -- applications of a rule to some items (the conclusion is left free)
        applications rule its =
            if List.length rule.premises > List.length its then
                []

            else
                choose (List.length rule.premises) its
                    |> List.concatMap (\chosen -> matchRule rule chosen Nothing |> List.map (\env -> ( chosen, env )))

        -- the formulas that an application gives: its conclusion, or the parts of the target that it can give (when
        -- the conclusion has letters that are not in the premises, as in ∨I or ⊥E)
        resultsOf rule ( chosen, env ) =
            case instantiate env rule.conclusion of
                Just f ->
                    if List.member f available then
                        []

                    else
                        [ ( chosen, f ) ]

                Nothing ->
                    List.filter (\g -> matchS rule.conclusion g env /= Nothing && not (List.member g available)) goalParts
                        |> List.map (Tuple.pair chosen)

        relevant chosen f =
            f
                == Insat
                || List.member f goalParts
                || List.any
                    (\it ->
                        case it of
                            ILine _ g ->
                                List.member f (subformulas g)

                            IBox _ _ a c ->
                                List.member f (subformulas a ++ subformulas c)
                    )
                    chosen

        hint kind rule chosen f txt =
            { kind = kind, rule = rule.name, refs = refsOf chosen, result = formulaToString f, input = formulaToInputString f, needs = [], assumptions = [], text = txt }

        forward =
            sys
                |> List.filter (\r -> useful r && not (List.isEmpty r.premises))
                |> List.concatMap
                    (\rule ->
                        applications rule items
                            |> List.concatMap (resultsOf rule)
                            |> List.filter (\( chosen, f ) -> relevant chosen f)
                            |> LE.uniqueBy (\( c, f ) -> ( List.map itemRef c, formulaToString f ))
                            |> List.map (\( chosen, f ) -> hint Forward rule chosen f (rule.name ++ " " ++ refsOf chosen ++ " gives " ++ formulaToString f))
                    )
                |> List.take limit

        closeParts =
            case ( target, problem.goal ) of
                ( Just t, _ ) ->
                    subformulas t

                ( Nothing, Just g ) ->
                    subformulas g

                _ ->
                    []

        -- closing the innermost subproof at the last line
        closing =
            case st.openAtEnd of
                b :: _ ->
                    let
                        outerItems =
                            accessible st forms n (List.take (List.length path - 1) path)
                    in
                    case Maybe.map2 (IBox b (n - 1)) (Dict.get b forms) (Dict.get (n - 1) forms) of
                        Just box ->
                            sys
                                |> List.filter (\r -> List.any isSubproof r.premises)
                                |> List.concatMap
                                    (\rule ->
                                        applications rule (box :: List.filter (\it -> itemRef it /= itemRef box) outerItems)
                                            |> List.filter (\( chosen, _ ) -> List.member box chosen)
                                            |> List.concatMap (resultsOf rule)
                                            |> List.filter (\( _, f ) -> f == Insat || List.member f closeParts || List.any (\g -> List.member f (subformulas g)) available)
                                            |> LE.uniqueBy (\( c, f ) -> ( List.map itemRef c, formulaToString f ))
                                            |> List.map
                                                (\( chosen, f ) ->
                                                    hint CloseSubproof rule chosen f ("close the subproof " ++ itemRef box ++ " and apply " ++ rule.name ++ " " ++ refsOf chosen ++ ": " ++ formulaToString f)
                                                )
                                    )
                                |> List.take limit

                        Nothing ->
                            []

                [] ->
                    []

        lineOf f =
            LE.findMap
                (\it ->
                    case it of
                        ILine i f2 ->
                            if f2 == f then
                                Just i

                            else
                                Nothing

                        _ ->
                            Nothing
                )
                items

        -- the ways of taking the formula premises of a rule from the lines (or leaving them to be proved)
        fill env ps =
            case ps of
                [] ->
                    [ env ]

                (PFormula s) :: more ->
                    (List.filterMap (\f -> matchS s f env) available ++ [ env ]) |> List.concatMap (\e -> fill e more)

                (PSubproof _ _) :: more ->
                    fill env more

        backward =
            case goal |> Maybe.andThen (\g -> if List.member g available then Nothing else Just g) of
                Just g ->
                    let
                        gs =
                            formulaToString g
                    in
                    sys
                        |> List.filter useful
                        |> List.concatMap
                            (\rule ->
                                case matchS rule.conclusion g Dict.empty of
                                    Just env ->
                                        fill env rule.premises |> List.map (\e -> ( rule, e ))

                                    Nothing ->
                                        []
                            )
                        |> List.filterMap
                            (\( rule, env ) ->
                                let
                                    formulaPremises =
                                        List.filterMap
                                            (\p ->
                                                case p of
                                                    PFormula s ->
                                                        Just s

                                                    _ ->
                                                        Nothing
                                            )
                                            rule.premises

                                    have =
                                        List.filterMap (\s -> instantiate env s |> Maybe.andThen lineOf) formulaPremises

                                    structural =
                                        case rule.conclusion of
                                            SMeta _ ->
                                                False

                                            _ ->
                                                True

                                    subproofOnly =
                                        List.isEmpty formulaPremises && not (List.isEmpty rule.premises)

                                    -- the premises that contain the conclusion (A → B in →E): one of them must be a line
                                    concMetas =
                                        schemaMetas rule.conclusion

                                    major =
                                        List.filter (\sch -> not (Set.isEmpty (Set.intersect concMetas (schemaMetas sch)))) formulaPremises

                                    majorAvailable =
                                        if List.isEmpty major then
                                            not (List.isEmpty have)

                                        else
                                            List.any (\sch -> instantiate env sch |> Maybe.andThen lineOf |> (/=) Nothing) major

                                    need p =
                                        case p of
                                            PFormula s ->
                                                case instantiate env s |> Maybe.andThen lineOf of
                                                    Just i ->
                                                        partialToString env s ++ " (line " ++ String.fromInt i ++ ")"

                                                    Nothing ->
                                                        partialToString env s

                                            PSubproof a c ->
                                                "a subproof from the assumption " ++ partialToString env a ++ " to " ++ partialToString env c

                                    needs =
                                        List.map need rule.premises
                                in
                                if structural || subproofOnly || majorAvailable then
                                    Just
                                        ( List.length have
                                        , { kind = Backward
                                          , rule = rule.name
                                          , refs = ""
                                          , result = gs
                                          , input = formulaToInputString g
                                          , needs = needs
                                          , assumptions =
                                                List.filterMap
                                                    (\p ->
                                                        case p of
                                                            PSubproof a _ ->
                                                                Maybe.map formulaToInputString (instantiate env a)

                                                            _ ->
                                                                Nothing
                                                    )
                                                    rule.premises
                                          , text =
                                                if List.isEmpty needs then
                                                    rule.name ++ " gives " ++ gs ++ " directly"

                                                else
                                                    rule.name ++ " gives " ++ gs ++ " from " ++ String.join "; " needs
                                          }
                                        )

                                else
                                    Nothing
                            )
                        |> LE.uniqueBy (\( _, h ) -> h.text)
                        |> List.sortBy (\( k, _ ) -> negate k)
                        |> List.map Tuple.second
                        |> List.take limit

                Nothing ->
                    []

        -- a backward hint whose premises are all lines is the same step as a forward one
        backwardDone =
            List.filter (\h -> not (List.isEmpty h.needs) && List.all (\x -> String.endsWith ")" x && String.contains "(line " x) h.needs) backward
                |> List.map (\h -> ( h.rule, h.result ))
    in
    closing ++ backward ++ List.filter (\h -> not (List.member ( h.rule, h.result ) backwardDone)) forward


schemaMetas : Schema -> Set String
schemaMetas s =
    case s of
        SMeta a ->
            Set.singleton a

        SNot a ->
            schemaMetas a

        SAnd a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        SOr a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        SImp a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        SIff a b ->
            Set.union (schemaMetas a) (schemaMetas b)

        _ ->
            Set.empty


subformulas : FormulaPL -> List FormulaPL
subformulas f =
    f
        :: (case f of
                Neg a ->
                    subformulas a

                Conj a b ->
                    subformulas a ++ subformulas b

                Disj a b ->
                    subformulas a ++ subformulas b

                Impl a b ->
                    subformulas a ++ subformulas b

                Equi a b ->
                    subformulas a ++ subformulas b

                _ ->
                    []
           )


isSubproof : Premise -> Bool
isSubproof p =
    case p of
        PSubproof _ _ ->
            True

        _ ->
            False



-- The sublists of k elements (in order).


choose : Int -> List a -> List (List a)
choose k xs =
    if k == 0 then
        [ [] ]

    else
        case xs of
            [] ->
                []

            x :: rest ->
                List.map ((::) x) (choose (k - 1) rest) ++ choose k rest
