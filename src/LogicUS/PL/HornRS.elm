module LogicUS.PL.HornRS exposing (
    HornFact, HornRule, HornKB
    ,  FwChRow, FwChResult, forwardChaining1, forwardChaining2, forwardChainingResultToString, forwardChainingResultToMDString
    , BwChRow, BwChResult, backwardChaining1, backwardChainingResultToString, backwardChainingResultToMDString
    , hornFactToFPL, hornKBToSPL, hornRuleToFPL, hornRulesToSPL, hornFactToClause, hornKBToClauses, hornRuleToClause, hornRulesToClauses
    , hornFactRead , hornFactReadFromString, hornFactReadExtraction, hornFactToInputString, hornKBRead, hornKBReadFromString, hornKBReadExtraction
    , hornKBToInputString, hornRuleRead, hornRuleReadFromString, hornRuleReadExtraction, hornRuleToInputString, hornRulesRead, hornRulesReadFromString, hornRulesReadExtraction, hornRulesToInputString
    ,hornFactToString, hornFactToMathString, hornKBToStringComma, hornKBToStringWedge, hornKBToMathStringComma, hornKBToMathStringWedge, hornRuleToString, hornRuleToMathString, hornRulesToString, hornRulesToMathString
    )

{-| The module provides the tools to work with Horn Reasoning Systems (HRS) through the definition of facts and rules and the use of forward and backward chaining to make deductions. Conversion to standard formulas and clauses is also provided to apply other algorithms on them.


# HRS Elements

@docs HornFact, HornRule, HornKB


# HRS Deductions I: Forward Chaining

@docs FwChRow, FwChResult, forwardChaining1, forwardChaining2, forwardChainingResultToString, forwardChainingResultToMDString


# HRS Deductions II: Backward Chaining

@docs BwChRow, BwChResult, backwardChaining1, backwardChainingResultToString, backwardChainingResultToMDString


# HRS Trasformations

@docs hornFactToFPL, hornKBToSPL, hornRuleToFPL, hornRulesToSPL, hornFactToClause, hornKBToClauses, hornRuleToClause, hornRulesToClauses


# HRS Parser

@docs hornFactRead, hornFactReadFromString, hornFactReadExtraction, hornFactToInputString, hornKBRead, hornKBReadFromString, hornKBReadExtraction, hornKBToInputString, hornRuleRead, hornRuleReadFromString, hornRuleReadExtraction, hornRuleToInputString, hornRulesRead, hornRulesReadFromString, hornRulesReadExtraction, hornRulesToInputString


# HRS Representations

@docs hornFactToString, hornFactToMathString, hornKBToStringComma, hornKBToStringWedge, hornKBToMathStringComma, hornKBToMathStringWedge, hornRuleToString, hornRuleToMathString, hornRulesToString, hornRulesToMathString

-}

--=========--
-- IMPORTS --
--=========--

import LogicUS.PL.AuxiliarFunctions as AUX exposing (parserErrorToString)
import LogicUS.PL.Clauses as PL_CL exposing (ClausePL, ClausePLSet)
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..), PSymb, SetPL)
import Parser exposing ((|.), (|=), Parser, Trailing(..))
import Set exposing (Set)



-- HRS ELEMENTS


{-| It defines a fact as a propositional variable. Use ("⟂", []) for represent inconsistence and ("⊤", []) for represent tautology.
-}
type alias HornFact =
    PSymb


{-| It defines a Knowledge Base of Horn as a set of facts.
-}
type alias HornKB =
    Set HornFact


{-| It defines an inference rule of Horn as a tuple whose first element regards to the antecedents of the rule and the second one to de consecuent of the rule.
-}
type alias HornRule =
    ( Set HornFact, HornFact )



-- HRS Deductions I: Forward Chaining


{-| It defines a row of a table of FC process with the properties:

  - step: indicates the step of the algorithm
  - kb: indicates the knowledge base handled at the regarding step
  - avRules : indicates the indices of rules available at the regarding step
  - shRules : indicates the indices of rules shooted at the regarding step
  - newFacts : indicates the new knowledge deducted at the regarding step

-}
type alias FwChRow =
    { step : Int
    , kb : HornKB
    , avRules : List Int
    , shRules : List Int
    , newFacts : HornKB
    }


{-| It holds the result of forward chaining process including rules, the initial KB, the goal, a table that summarizes the development of the algorithm and the result (if the goal can be deducted from initial KB with the rules given )
-}
type alias FwChResult =
    { rules : List HornRule
    , initialKB : HornKB
    , goal : HornFact
    , table : List FwChRow
    , res : Bool
    }


{-| It performs forwardChaining algorithm with removing, at each step, the rules shot from available rules.
-}
forwardChaining1 : List HornRule -> HornKB -> HornFact -> FwChResult
forwardChaining1 rules facts goal =
    let
        avRules =
            AUX.uniqueConcatList [] rules
    in
    if Set.member goal facts then
        { rules = avRules, initialKB = facts, goal = goal, table = [], res = True }

    else
        let
            ( res, table ) =
                forwardChainingAux1 (List.indexedMap Tuple.pair <| List.map (\( ra, rc ) -> ( Set.toList ra, rc )) avRules) facts goal 1
        in
        { rules = avRules, initialKB = facts, goal = goal, table = table, res = res }


forwardChainingAux1 : List ( Int, ( List PSymb, PSymb ) ) -> HornKB -> HornFact -> Int -> ( Bool, List FwChRow )
forwardChainingAux1 avRules kb goal step =
    let
        ( shooted, rem ) =
            List.partition (\( _, ( ra, _ ) ) -> List.all (\s -> Set.member s kb) ra) avRules
    in
    let
        newFacts =
            Set.diff (Set.fromList <| List.map (Tuple.second << Tuple.second) shooted) kb
    in
    let
        row =
            { step = step, kb = kb, avRules = List.map Tuple.first avRules, shRules = List.map Tuple.first shooted, newFacts = newFacts }
    in
    if Set.isEmpty newFacts then
        ( False, [ row ] )

    else if Set.member goal newFacts then
        ( True, [ row ] )

    else
        let
            ( res, tableTail ) =
                forwardChainingAux1 rem (Set.union kb newFacts) goal (step + 1)
        in
        ( res, row :: tableTail )


{-| It performs forwardChaining algorithm with removing, at each step, the rules whose consecuent is already in the KB from available rules.
-}
forwardChaining2 : List HornRule -> HornKB -> HornFact -> FwChResult
forwardChaining2 rules facts goal =
    let
        avRules =
            AUX.uniqueConcatList [] rules
    in
    if Set.member goal facts then
        { rules = avRules, initialKB = facts, goal = goal, table = [], res = True }

    else
        let
            ( res, table ) =
                forwardChainingAux2 (List.indexedMap Tuple.pair <| List.map (\( ra, rc ) -> ( Set.toList ra, rc )) <| List.filter (\( _, rc ) -> not <| Set.member rc facts) avRules) facts goal 1
        in
        { rules = avRules, initialKB = facts, goal = goal, table = table, res = res }


forwardChainingAux2 : List ( Int, ( List PSymb, PSymb ) ) -> HornKB -> HornFact -> Int -> ( Bool, List FwChRow )
forwardChainingAux2 avRules kb goal step =
    let
        ( shooted, rem ) =
            List.partition (\( _, ( ra, _ ) ) -> List.all (\s -> Set.member s kb) ra) avRules
    in
    let
        newFacts =
            Set.diff (Set.fromList <| List.map (Tuple.second << Tuple.second) shooted) kb
    in
    let
        row =
            { step = step, kb = kb, avRules = List.map Tuple.first avRules, shRules = List.map Tuple.first shooted, newFacts = newFacts }
    in
    if Set.isEmpty newFacts then
        ( False, [ row ] )

    else if Set.member goal newFacts then
        ( True, [ row ] )

    else
        let
            ( res, tableTail ) =
                forwardChainingAux1 (List.filter (\( _, ( _, rc ) ) -> not <| Set.member rc newFacts) rem) (Set.union kb newFacts) goal (step + 1)
        in
        ( res, row :: tableTail )


{-| It generates a markdown string (including latex notation) of the result of a forwarding chaining execution.
-}
forwardChainingResultToMDString : FwChResult -> String
forwardChainingResultToMDString res =
    let
        fchrowToTableMathString row =
            [ String.fromInt row.step
            , hornKBToMathStringComma row.kb
            , if List.isEmpty row.avRules then
                "-"

              else
                String.join ", " <| List.map (\i -> "R_{" ++ String.fromInt (i + 1) ++ "}") row.avRules
            , if List.isEmpty row.shRules then
                "-"

              else
                String.join ", " <| List.map (\i -> "R_{" ++ String.fromInt (i + 1) ++ "}") row.shRules
            , if Set.isEmpty row.newFacts then
                "-"

              else
                hornKBToMathStringComma row.newFacts
            ]
    in
    let
        initialfacts =
            "- <span style=\"font-variant:small-caps;\">Initial Facts</span> : $ " ++ hornKBToMathStringComma res.initialKB ++ " $"

        rules =
            "- <span style=\"font-variant:small-caps;\">Rules</span>: " ++ hornRulesToMathString res.rules

        goal =
            "- <span style=\"font-variant:small-caps;\">Goal</span> : $ " ++ (PL_SS.fplToMathString <| Atom res.goal) ++ " $"

        result =
            if res.res then
                "- <span style=\"font-variant:small-caps;\">Result</span> : **TRUE**"

            else
                "- <span style=\"font-variant:small-caps;\">Result</span> : **FALSE**"

        table =
            AUX.fromListToTableLatex (String.repeat 5 "|c" ++ "|") [ [ "Step", "Knowledge \\, Base", "Available \\, Rules", "Shooted \\, Rules", "Deductions" ] ] (List.map fchrowToTableMathString res.table) []
    in
    initialfacts ++ "\n" ++ rules ++ "\n" ++ goal ++ "\n" ++ result ++ "\n" ++ "$$" ++ table ++ "$$"


{-| It generates two tables in a list with the result and the process of a forwarding chaining execution.
-}
forwardChainingResultToString : FwChResult -> List String
forwardChainingResultToString res =
    let
        fchrowToTableString row =
            String.join ";" <|
                [ String.fromInt row.step
                , hornKBToStringComma row.kb
                , if List.isEmpty row.avRules then
                    "-"

                  else
                    String.join ", " <| List.map (\i -> "R" ++ (AUX.replaceBySubscript <| String.fromInt (i + 1))) row.avRules
                , if List.isEmpty row.shRules then
                    "-"

                  else
                    String.join ", " <| List.map (\i -> "R" ++ (AUX.replaceBySubscript <| String.fromInt (i + 1))) row.shRules
                , if Set.isEmpty row.newFacts then
                    "-"

                  else
                    hornKBToStringComma row.newFacts
                ]
    in
    let
        initialfacts =
            String.join ";" <| [ "Initial facts", hornKBToStringWedge res.initialKB ]

        rules =
            String.join ";" <| [ "Rules", hornRulesToString res.rules ]

        goal =
            String.join ";" <| [ "Goal", hornFactToString res.goal ]

        result =
            String.join ";" <|
                [ "RESULT"
                , if res.res then
                    "TRUE"

                  else
                    "FALSE"
                ]
    in
    [ initialfacts ++ "\n" ++ rules ++ "\n" ++ goal ++ "\n" ++ result
    , String.join "\n" <| "Step;Knowledge Base;Available Rules;Shooted Rules;Deductions" :: List.map fchrowToTableString res.table
    ]



--================================= BACKWARD CHAINING ====================================--


{-| It defines a row of a table of BW process with the properties:

  - step: indicates the step of the algorithm
  - opened: indicates the opened ways at the regarding step
  - currentNode : indicates the way treated at the regarding step
  - goal : indicates the goal of currentNode way treated at the regarding step
  - descendents : indicates the new ways deducted at the regarding step

-}
type alias BwChRow =
    { step : Int
    , opened : List ( Bool, HornKB )
    , currentNode : Maybe HornKB
    , goal : Maybe HornFact
    , descendents : List ( Bool, Int, List ( Bool, HornFact ) )
    }


{-| It holds the result of backward chaining process including rules, the initial KB, the goal, a table that summarizes the development of the algorithm and the result (if the goal can be deducted from initial KB with the rules given).
-}
type alias BwChResult =
    { rules : List HornRule
    , initialKB : HornKB
    , goal : HornFact
    , table : List BwChRow
    , res : Bool
    }


{-| It performs the backward chaining algorithm by selecting at each step the way with the fewest remaining goals and the goal using alphabetical order.
-}
backwardChaining1 : List HornRule -> HornKB -> HornFact -> BwChResult
backwardChaining1 rules facts goal =
    let
        avRules =
            AUX.uniqueConcatList [] rules
    in
    if Set.member goal facts then
        { rules = avRules, initialKB = facts, goal = goal, table = [], res = True }

    else
        let
            ( res, table ) =
                backwardChainingAux1 (List.indexedMap Tuple.pair avRules) [ Set.fromList [ goal ] ] [] [] facts 1
        in
        { rules = avRules, initialKB = facts, goal = goal, table = table, res = res }


backwardChainingAux1 :
    List ( Int, HornRule )
    -> List HornKB
    -> List HornKB
    -> List HornKB
    -> HornKB
    -> Int
    -> ( Bool, List BwChRow )
backwardChainingAux1 rules opened cancelOpened explored facts step =
    case opened of
        [] ->
            ( False, [ { step = step, opened = List.map (\y -> ( False, y )) cancelOpened, currentNode = Nothing, goal = Nothing, descendents = [] } ] )

        x :: xs ->
            case Set.toList x of
                [] ->
                    ( True, [ { step = step, opened = List.map (\y -> ( True, y )) opened ++ List.map (\y -> ( False, y )) cancelOpened, currentNode = Just Set.empty, goal = Nothing, descendents = [] } ] )

                g :: gs ->
                    let
                        desc =
                            List.indexedMap
                                (\i ( ri, ( ra, _ ) ) ->
                                    ( i
                                    , ( ri, Set.union ra (Set.fromList gs) )
                                    )
                                )
                            <|
                                List.filter (\( _, ( _, rc ) ) -> rc == g) rules
                    in
                    let
                        ( notabsDesc, absDesc ) =
                            descendentsAbsorption desc (opened ++ explored) facts
                    in
                    let
                        ( openedSurvival, newCancelOpened ) =
                            List.partition (\igs -> List.all (\dgs -> not <| Set.isEmpty <| Set.diff dgs igs) notabsDesc) xs
                    in
                    let
                        newOpened =
                            List.sortBy Set.size <| (openedSurvival ++ notabsDesc)
                    in
                    let
                        ( res, tableRows ) =
                            backwardChainingAux1 rules newOpened newCancelOpened (explored ++ [ x ]) facts (step + 1)

                        descendents =
                            List.map
                                (\( i, ( ri, igs ) ) ->
                                    ( not <| List.member i absDesc
                                    , ri
                                    , List.map (\gi -> ( not <| Set.member gi facts, gi )) <| Set.toList igs
                                    )
                                )
                                desc
                    in
                    ( res
                    , { step = step
                      , opened = List.map (\y -> ( True, y )) opened ++ List.map (\y -> ( False, y )) cancelOpened
                      , currentNode = Just x
                      , goal = Just g
                      , descendents = descendents
                      }
                        :: tableRows
                    )


descendentsAbsorption : List ( Int, ( Int, HornKB ) ) -> List HornKB -> HornKB -> ( List HornKB, List Int )
descendentsAbsorption desc ref facts =
    List.foldl
        (\( i, dgs ) ( notabs, abs ) ->
            if List.any (\igs -> Set.isEmpty <| Set.diff igs dgs) (ref ++ notabs) then
                ( notabs, i :: abs )

            else
                ( notabs ++ [ dgs ], abs )
        )
        ( [], [] )
        (List.sortBy (Set.size << Tuple.second) <| List.map (\( i, ( _, dgs ) ) -> ( i, Set.filter (\g -> not <| Set.member g facts) dgs )) desc)


{-| It generates a MD string (including latex notation) of the result of an execution of BC algorithm
-}
backwardChainingResultToMDString : BwChResult -> String
backwardChainingResultToMDString res =
    let
        bwchrowToTableMathString row =
            [ String.fromInt row.step
            , if List.isEmpty row.opened then
                "-"

              else
                String.join ", " <|
                    List.map
                        (\( ncancel, gs ) ->
                            if ncancel then
                                "\\{" ++ hornKBToMathStringComma gs ++ "\\}"

                            else
                                "\\cancel{ \\{" ++ hornKBToMathStringComma gs ++ "\\} }"
                        )
                        row.opened
            , Maybe.withDefault "-" <| Maybe.map (\x -> "\\{" ++ hornKBToMathStringComma x ++ "\\}") row.currentNode
            , Maybe.withDefault "-" <| Maybe.map hornFactToMathString row.goal
            , if List.isEmpty row.descendents then
                "-"

              else
                String.join ", " <|
                    List.map
                        (\( ncancel, ri, gs ) ->
                            if ncancel then
                                " (R_{"
                                    ++ String.fromInt (ri + 1)
                                    ++ "}, \\{"
                                    ++ (String.join "," <|
                                            List.map
                                                (\( nf, g ) ->
                                                    if nf then
                                                        hornFactToMathString g

                                                    else
                                                        "\\boldsymbol{" ++ hornFactToMathString g ++ "}"
                                                )
                                                gs
                                       )
                                    ++ "\\})"

                            else
                                "\\cancel{ (R_{"
                                    ++ String.fromInt (ri + 1)
                                    ++ "}, \\{"
                                    ++ (String.join "," <|
                                            List.map
                                                (\( nf, g ) ->
                                                    if nf then
                                                        hornFactToMathString g

                                                    else
                                                        "\\boldsymbol{" ++ hornFactToMathString g ++ "}"
                                                )
                                                gs
                                       )
                                    ++ "\\})}"
                        )
                        row.descendents
            ]
    in
    let
        initialfacts =
            "- <span style=\"font-variant:small-caps;\">Initial Facts</span> : $ " ++ hornKBToMathStringComma res.initialKB ++ " $"

        rules =
            "- <span style=\"font-variant:small-caps;\">Rules</span>: " ++ hornRulesToMathString res.rules

        goal =
            "- <span style=\"font-variant:small-caps;\">Goal</span> : $ " ++ (PL_SS.fplToMathString <| Atom res.goal) ++ " $"

        result =
            if res.res then
                "- <span style=\"font-variant:small-caps;\">Result</span> : **TRUE**"

            else
                "- <span style=\"font-variant:small-caps;\">Result</span> : **FALSE**"

        table =
            AUX.fromListToTableLatex (String.repeat 5 "|c" ++ "|") [ [ "Step", "Opened \\, ways", "Selected \\, way", "Selected \\, Goal", "New Ways" ] ] (List.map bwchrowToTableMathString res.table) []
    in
    initialfacts ++ "\n" ++ rules ++ "\n" ++ goal ++ "\n" ++ result ++ "\n" ++ "$$" ++ table ++ "$$"


{-| It generates two tables in a list with the result and the process of a backwarding chaining execution.
-}
backwardChainingResultToString : BwChResult -> List String
backwardChainingResultToString res =
    let
        bchrowToTableString row =
            String.join ";" <|
                [ String.fromInt row.step
                , if List.isEmpty row.opened then
                    "-"

                  else
                    String.join ", " <|
                        List.map
                            (\( ncancel, gs ) ->
                                if ncancel then
                                    "{" ++ hornKBToStringComma gs ++ "}"

                                else
                                    "<del>{" ++ hornKBToStringComma gs ++ "}</del>"
                            )
                            row.opened
                , Maybe.withDefault "-" <| Maybe.map (\x -> "{" ++ hornKBToStringComma x ++ "}") row.currentNode
                , Maybe.withDefault "-" <| Maybe.map hornFactToString row.goal
                , if List.isEmpty row.descendents then
                    "-"

                  else
                    String.join ", " <|
                        List.map
                            (\( ncancel, ri, gs ) ->
                                if ncancel then
                                    " (R"
                                        ++ (AUX.replaceBySubscript <| String.fromInt (ri + 1))
                                        ++ ", {"
                                        ++ (String.join "," <|
                                                List.map
                                                    (\( nf, g ) ->
                                                        if nf then
                                                            hornFactToString g

                                                        else
                                                            "<b>" ++ hornFactToString g ++ "</b>"
                                                    )
                                                    gs
                                           )
                                        ++ "})"

                                else
                                    "<del> (R"
                                        ++ (AUX.replaceBySubscript <| String.fromInt (ri + 1))
                                        ++ ", {"
                                        ++ (String.join "," <|
                                                List.map
                                                    (\( nf, g ) ->
                                                        if nf then
                                                            hornFactToString g

                                                        else
                                                            "<b>" ++ hornFactToString g ++ "</b>"
                                                    )
                                                    gs
                                           )
                                        ++ "})</del>"
                            )
                            row.descendents
                ]
    in
    let
        initialfacts =
            String.join ";" <| [ "Initial facts", hornKBToStringWedge res.initialKB ]

        rules =
            String.join ";" <| [ "Rules", hornRulesToString res.rules ]

        goal =
            String.join ";" <| [ "Goal", hornFactToString res.goal ]

        result =
            String.join ";" <|
                [ "RESULT"
                , if res.res then
                    "TRUE"

                  else
                    "FALSE"
                ]
    in
    [ initialfacts ++ "\n" ++ rules ++ "\n" ++ goal ++ "\n" ++ result
    , String.join "\n" <| "Step;Opened ways;Selected way;Selected Goal;New Ways" :: List.map bchrowToTableString res.table
    ]



-- PARSER
{-| It reads a Horn fact from a string. The string may correspond to:

  - A string of uppercase letters optionaly subindexed using "_{" "}" as delimiters and integers separated by commas as indices. Ex: "P", "PAUL", "P_{1}", "PAUL\_{1,2,3}"
  - A string with "!F" that represents inconsistence.
  - A string with "!T" that represents tautology.


-}
hornFactRead : String -> HornFact
hornFactRead = ( hornFactReadExtraction << hornFactReadFromString)

{-| It reads a Horn fact from a string. The string may correspond to:

  - A string of uppercase letters optionaly subindexed using "_{" "}" as delimiters and integers separated by commas as indices. Ex: "P", "PAUL", "P_{1}", "PAUL\_{1,2,3}"
  - A string with "!F" that represents inconsistence.
  - A string with "!T" that represents tautology.

It gives a tuple with the Horn fact (if it could be read) , otherwise, the false fact is given. 

-}
hornFactReadFromString : String -> ( Maybe HornFact, String, String )
hornFactReadFromString x =
    case AUX.cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        s ->
            case Parser.run hornFactOnlyParser s of
                Ok y ->
                    ( Maybe.Just y, hornFactToInputString y, "" )

                Err y ->
                    ( Maybe.Nothing, s, parserErrorToString s 0 y )


{-| It extract the Horn fact read. If it is not present it returns a fact of inconsistency
-}
hornFactReadExtraction : ( Maybe HornFact, String, String ) -> HornFact
hornFactReadExtraction ( mf, _, _ ) =
    Maybe.withDefault ( "⟂", [] ) mf


{-| It generates the string that corresponds to the input of a given Horn fact
-}
hornFactToInputString : HornFact -> String
hornFactToInputString hf =
    case hf of
        ( vname, [] ) ->
            String.toUpper vname

        ( vname, vindices ) ->
            String.toUpper vname ++ "_{" ++ (String.join "," <| List.map String.fromInt vindices) ++ "}"


hornFactSymbParser : Parser String
hornFactSymbParser =
    Parser.succeed ()
        |. Parser.chompIf Char.isUpper
        |. Parser.chompWhile Char.isAlphaNum
        |> Parser.getChompedString


hornFactSubindexedParser : Parser ( String, List Int )
hornFactSubindexedParser =
    Parser.succeed Tuple.pair
        |= hornFactSymbParser
        |= Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Parser.int
            , trailing = Forbidden
            }


hornFactParser : Parser ( String, List Int )
hornFactParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable hornFactSubindexedParser
        , Parser.succeed (\x -> ( x, [] ))
            |= hornFactSymbParser
        , Parser.succeed ( "⟂", [] )
            |. Parser.symbol "!F"
        , Parser.succeed ( "⊤", [] )
            |. Parser.symbol "!T"
        ]


hornFactOnlyParser : Parser ( String, List Int )
hornFactOnlyParser =
    Parser.succeed identity
        |= hornFactParser
        |. Parser.end

{-| It reads a Horn KB from a string. The string has to match to a serial of facts separated by commas, following the rules defined for facts parsing.

It gives the Horn KB (if it could be read), or the empty set (if it couldn't).
-}

hornKBRead : String -> HornKB
hornKBRead = (hornKBReadExtraction << hornKBReadFromString)

{-| It reads a Horn KB from a string. The string has to match to a serial of facts separated by commas, following the rules defined for facts parsing.

It gives a tuple with the Horn KB (if it could be read) , the input string and the message of error (if fact couldn't be read).

-}
hornKBReadFromString : String -> ( Maybe HornKB, String, String )
hornKBReadFromString x =
    case AUX.cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        s ->
            case Parser.run hornKBParser s of
                Ok y ->
                    ( Maybe.Just y, hornKBToInputString y, "" )

                Err y ->
                    ( Maybe.Nothing, s, parserErrorToString s 0 y )


{-| It extract the Horn KB read. If it is not present it returns an empty set
-}
hornKBReadExtraction : ( Maybe HornKB, String, String ) -> HornKB
hornKBReadExtraction ( mkb, _, _ ) =
    Maybe.withDefault Set.empty mkb


{-| It generates the string that corresponds to the input of a given Horn KB
-}
hornKBToInputString : HornKB -> String
hornKBToInputString kb =
    String.join " & " <| List.map hornFactToInputString <| Set.toList kb


hornKBParser : Parser HornKB
hornKBParser =
    Parser.succeed Set.fromList
        |= Parser.sequence
            { start = ""
            , separator = ","
            , end = ""
            , spaces = Parser.spaces
            , item = hornFactParser
            , trailing = Forbidden
            }
        |. Parser.end


{-| It reads a Horn rule from a string. The string has to match to a serial of facts separated by `&` for the antecedents, followed by the symbol `->` and a unique fact as consecuent.

It gives the Horn rule (if it could be read), otherwise, ⊥ -> ⊥ is given.
-}
hornRuleRead : String -> HornRule
hornRuleRead = (hornRuleReadExtraction << hornRuleReadFromString)

{-| It reads a Horn rule from a string. The string has to match to a serial of facts separated by `&` for the antecedents, followed by the symbol `->` and a unique fact as consecuent.

It gives a tuple with the Horn rule (if it could be read) , the input string and the message of error (if rule couldn't be read).

-}
hornRuleReadFromString : String -> ( Maybe HornRule, String, String )
hornRuleReadFromString x =
    case AUX.cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        s ->
            case Parser.run hornRuleParser s of
                Ok y ->
                    ( Maybe.Just y, (String.join " & " <| List.map hornFactToInputString <| Set.toList <| Tuple.first y) ++ "->" ++ (hornFactToInputString <| Tuple.second y), "" )

                Err y ->
                    ( Maybe.Nothing, s, parserErrorToString s 0 y )


{-| It extract the Horn rule read. If it is not present it returns a rule with inconsistence as antecedent and consecuent
-}
hornRuleReadExtraction : ( Maybe HornRule, String, String ) -> HornRule
hornRuleReadExtraction ( mr, _, _ ) =
    Maybe.withDefault ( Set.singleton ( "⟂", [] ), ( "⟂", [] ) ) mr


{-| It generates the string that corresponds to the input of a given Horn rule
-}
hornRuleToInputString : HornRule -> String
hornRuleToInputString ( ra, rc ) =
    hornKBToInputString ra ++ " -> " ++ hornFactToInputString rc


hornRuleParser : Parser HornRule
hornRuleParser =
    Parser.succeed Tuple.pair
        |= hornLHSParser
        |. Parser.symbol "->"
        |= hornFactParser
        |. Parser.end


hornLHSParser : Parser HornKB
hornLHSParser =
    Parser.sequence
        { start = ""
        , separator = "&"
        , end = ""
        , spaces = Parser.spaces
        , item = hornFactParser
        , trailing = Forbidden
        }
        |> Parser.map Set.fromList


{-| It reads a Horn rule list from a string. The string has to match to a serial of rules separated by commas.

It gives a tuple with the Horn rule list (if it could be read) , the empty list (if it couldn't).
-}

hornRulesRead : String -> List HornRule
hornRulesRead = (hornRulesReadExtraction << hornRulesReadFromString)

{-| It reads a Horn rule list from a string. The string has to match to a serial of rules separated by commas.

It gives a tuple with the Horn rule list (if it could be read) , the input string and the message of error (if fact couldn't be read).

-}
hornRulesReadFromString : String -> ( Maybe (List HornRule), String, String )
hornRulesReadFromString x =
    case AUX.cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        s ->
            case Parser.run hornRulesParser s of
                Ok y ->
                    ( Maybe.Just y, hornRulesToInputString y, "" )

                Err y ->
                    ( Maybe.Nothing, s, parserErrorToString s 0 y )


{-| It extract the list of Horn rules read. If it is not present it returns an empty list
-}
hornRulesReadExtraction : ( Maybe (List HornRule), String, String ) -> List HornRule
hornRulesReadExtraction ( rs, _, _ ) =
    Maybe.withDefault [] rs


{-| It generates the string that corresponds to the input of a given list of Horn rules
-}
hornRulesToInputString : List HornRule -> String
hornRulesToInputString rs =
    String.join ", " <| List.map hornRuleToInputString rs


hornRulesParser : Parser (List HornRule)
hornRulesParser =
    Parser.succeed identity
        |= Parser.sequence
            { start = ""
            , separator = ","
            , end = ""
            , spaces = Parser.spaces
            , item =
                Parser.succeed Tuple.pair
                    |= hornLHSParser
                    |. Parser.symbol "->"
                    |= hornFactParser
            , trailing = Forbidden
            }
        |. Parser.end



-- Transformations


{-| It transform a Horn fact to a standard formula
-}
hornFactToFPL : HornFact -> FormulaPL
hornFactToFPL f =
    Atom f


{-| It transform a Horn KB to a standard formula set
-}
hornKBToSPL : HornKB -> SetPL
hornKBToSPL kb =
    List.map hornFactToFPL <| Set.toList kb


{-| It transform a Horn rule to a standard formula
-}
hornRuleToFPL : HornRule -> FormulaPL
hornRuleToFPL ( ra, rc ) =
    Impl (PL_SS.splConjunction <| hornKBToSPL ra) (Atom rc)


{-| It transform a list of Horn rules to a standard formula
-}
hornRulesToSPL : List HornRule -> SetPL
hornRulesToSPL rs =
    List.map hornRuleToFPL rs


{-| It transform a Horn fact to a clause
-}
hornFactToClause : HornFact -> ClausePL
hornFactToClause f =
    [ ( f, True ) ]


{-| It transform a Horn kb to a set of clauses
-}
hornKBToClauses : HornKB -> ClausePLSet
hornKBToClauses kb =
    List.map hornFactToClause <| Set.toList kb


{-| It transform a Horn rule to a clause
-}
hornRuleToClause : HornRule -> ClausePL
hornRuleToClause ( ra, rc ) =
    PL_CL.cplSort <| (List.map (\x -> ( x, False )) <| Set.toList ra) ++ [ ( rc, True ) ]


{-| It transform a list of Horn rules to a set of clauses
-}
hornRulesToClauses : List HornRule -> ClausePLSet
hornRulesToClauses rs =
    List.map hornRuleToClause rs



-- HRS String Represent ation


{-| It gives the string representation of a Horn fact using unicode notation
-}
hornFactToString : HornFact -> String
hornFactToString ( h, pindices ) =
    if List.isEmpty pindices then
        h

    else
        h ++ (AUX.replaceBySubscript <| (String.join "," <| List.map String.fromInt pindices))


{-| It gives the string representation of a Horn fact using latex notation
-}
hornFactToMathString : HornFact -> String
hornFactToMathString ( h, pindices ) =
    if List.isEmpty pindices then
        h

    else
        h ++ "_{" ++ (String.join "," <| List.map String.fromInt pindices) ++ "}"


{-| It gives the string representation of a Horn KB separating facts by comma using unicode notation
-}
hornKBToStringComma : HornKB -> String
hornKBToStringComma kb =
    String.join ", " <| List.map hornFactToString <| Set.toList kb


{-| It gives the string representation of a Horn KB separating facts by comma using latex notation
-}
hornKBToMathStringComma : HornKB -> String
hornKBToMathStringComma kb =
    String.join ", " <| List.map hornFactToMathString <| Set.toList kb


{-| It gives the string representation of a Horn KB separating facts by ∧ using unicode notation
-}
hornKBToStringWedge : HornKB -> String
hornKBToStringWedge kb =
    String.join " ∧ " <| List.map hornFactToString <| Set.toList kb


{-| It gives the string representation of a Horn KB separating facts by ∧ using latex notation
-}
hornKBToMathStringWedge : HornKB -> String
hornKBToMathStringWedge kb =
    String.join " \\wedge " <| List.map hornFactToMathString <| Set.toList kb


{-| It gives the string representation of a Horn rule using unicode notation
-}
hornRuleToString : HornRule -> String
hornRuleToString ( ra, rc ) =
    hornKBToStringWedge ra ++ " → " ++ hornFactToString rc


{-| It gives the string representation of a Horn rule using latex notation
-}
hornRuleToMathString : HornRule -> String
hornRuleToMathString ( ra, rc ) =
    hornKBToMathStringWedge ra ++ " \\rightarrow " ++ hornFactToMathString rc


{-| It gives the string representation of a Horn rule list using unicode notation and indexing the formulas by its position in the list
-}
hornRulesToString : List HornRule -> String
hornRulesToString rs =
    String.join ", " <| List.indexedMap (\i r -> AUX.replaceBySubscript "R" ++ String.fromInt (i + 1) ++ " : " ++ hornRuleToString r) rs


{-| It gives the string representation of a Horn rule list using latex notation and indexing the formulas by its position in the list
-}
hornRulesToMathString : List HornRule -> String
hornRulesToMathString rs =
    String.join ", " <| List.indexedMap (\i r -> "$R_{" ++ String.fromInt (i + 1) ++ "} \\equiv " ++ hornRuleToMathString r ++ "$") rs
