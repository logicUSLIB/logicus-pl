module LogicUS.PL.Clauses exposing
    ( ClausePLLiteral, ClausePL, ClausePLSet
    , cplSort, cplIsPositive, cplIsNegative, cplSubsumes, cplIsTautology, csplRemoveEqClauses, csplRemoveTautClauses, csplRemoveSubsumedClauses, cplSymbols, csplSymbols, cplInterpretations, csplInterpretations, cplValuation, csplValuation, cplModels, csplModels, cplIsInsat, csplIsTaut, csplIsSat, csplIsInsat
    , clauseLitToLiteral, csplFromCNF, fplToClauses, splToClauses, fplToClausesTseitin, splToClausesTseitin
    , cplRead, cplReadFromString, cplReadExtraction, cplToInputString
    , cplToString, cplToMathString, csplToString, csplToMathString, csplToDIMACS
    )

{-| The module provides the tools for express formulas in their Clausal Form.


# Types

@docs ClausePLLiteral, ClausePL, ClausePLSet


# Work with clauses

@docs cplSort, cplIsPositive, cplIsNegative, cplSubsumes, cplIsTautology, csplRemoveEqClauses, csplRemoveTautClauses, csplRemoveSubsumedClauses, cplSymbols, csplSymbols, cplInterpretations, csplInterpretations, cplValuation, csplValuation, cplModels, csplModels, cplIsInsat, csplIsTaut, csplIsSat, csplIsInsat


# Formulas and Clauses

@docs clauseLitToLiteral, csplFromCNF, fplToClauses, splToClauses, fplToClausesTseitin, splToClausesTseitin


# Clauses Parser

@docs cplRead , cplReadFromString, cplReadExtraction, cplToInputString


# Clauses Representation

@docs cplToString, cplToMathString, csplToString, csplToMathString, csplToDIMACS

-}

--=========--
-- IMPORTS --
--=========--

import Dict exposing (Dict)
import LogicUS.PL.AuxiliarFunctions exposing (cleanSpaces, parserErrorToString, powerset, uniqueConcatList)
import LogicUS.PL.NormalForms as PL_NF
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..), Interpretation, Literal, PSymb, SetPL)
import Parser exposing ((|.), (|=), Parser, Trailing(..))



--=======--
-- TYPES --
--=======--


{-| It represent a literal of a clause as a tuple with the symbol of the literal (string) and the sign of the literal (False:negative literal, True:positive literal).
-}
type alias ClausePLLiteral =
    ( PSymb, Bool )


{-| It represent a set of clause literals.

    c1 : ClausePL
    c1 =
        [ ( "p", False ), ( "q", False ), ( "r", True ) ]

    c2 : ClausePL
    c2 =
        [ ( "p", False ), ( "r", True ) ]

    c3 : ClausePL
    c3 =
        [ ( "r", True ) ]

-}
type alias ClausePL =
    List ClausePLLiteral


{-| It represent a set of ClausePL

    cs : ClausePLSet
    cs =
        [ c1, c2, c3 ]

-}
type alias ClausePLSet =
    List ClausePL



-----------------------
-- Auxiliar functions -
-----------------------
-- It compare two clause literals by the comparision of their symbols and in equality conditions comparing their signs (False < True).


compareClausePLLiterals : ( PSymb, Bool ) -> ( PSymb, Bool ) -> Order
compareClausePLLiterals ( symb1, sign1 ) ( symb2, sign2 ) =
    case ( sign1, sign2 ) of
        ( True, False ) ->
            LT

        ( False, True ) ->
            GT

        _ ->
            compare symb1 symb2



-------------------
-- Work functions -
-------------------


{-| It sorts the literals of the clause by alphabetical order.
-}
cplSort : ClausePL -> ClausePL
cplSort cs =
    List.sortWith compareClausePLLiterals cs


{-| Indicates if the first clause subsumes the second, that is, if the first is entirely contained in the second.

    cplSubsumes c1 c2 == False

    cplSubsumes c2 c1 == True

-}
cplSubsumes : ClausePL -> ClausePL -> Bool
cplSubsumes c1 c2 =
    List.all (\x -> List.member x c2) c1


{-| Indicates if the clause is a tautology, that is if it contains a literal and its complement.

    cplIsTautology c1 == False

    (cplIsTautology <| c1 ++ [ ( "p", True ) ]) == True

-}
cplIsTautology : ClausePL -> Bool
cplIsTautology c =
    List.any (\( psymb, sign ) -> List.member ( psymb, not sign ) c) c


{-| Indicates if the clause is enterly positive, this is with all its literals positive

    cplIsPositive c1 == False

    cplIsPositive c3 == True

-}
cplIsPositive : ClausePL -> Bool
cplIsPositive c =
    List.all Tuple.second c


{-| Indicates if the clause is enterly negative, this is with all its literals negative

    cplIsNegative c1 == False

    cplIsNegative (List.take 2 c1) == True

-}
cplIsNegative : ClausePL -> Bool
cplIsNegative c =
    List.all (not << Tuple.second) c


{-| It removes clauses that are equal from a list of clauses

    cs1 = [c1, c2, c3]

    csplRemoveEqClauses cs1 == cs1

    csplRemoveEqClauses (cs1 ++ (List.map (List.reverse) cs1)) == cs1

-}
csplRemoveEqClauses : ClausePLSet -> ClausePLSet
csplRemoveEqClauses xs =
    uniqueConcatList [] <| List.map cplSort xs


{-| It removes clauses that are tautological clauses

    csplRemoveTautClauses <| List.map (\\x -> x ++ [("q", True)]) cs1 ==
        [[("p",False),("r",True),("q",True)],[("r",True),("q",True)]]

-}
csplRemoveTautClauses : ClausePLSet -> ClausePLSet
csplRemoveTautClauses cs =
    List.filter (not << cplIsTautology) <| List.map cplSort cs


{-| It removes clauses that are subsumed by other from the list

    csplRemoveSubsumedClauses cs1 == [ [ Atom "r" ] ]

-}
csplRemoveSubsumedClauses : ClausePLSet -> ClausePLSet
csplRemoveSubsumedClauses cs =
    List.foldl
        (\c ac ->
            if List.any (\x -> cplSubsumes x c) ac then
                ac

            else
                List.filter (not << cplSubsumes c) ac ++ [ c ]
        )
        []
        (List.map cplSort cs)


{-| It gives the propositional symbols that take place in the clause

    cplSymbols c1 =
        [ "p", "q", "r" ]
    cplSymbols c2 =
        [ "p", "r" ]
    cplSymbols c3 =
        [ "r" ]

-}
cplSymbols : ClausePL -> List PSymb
cplSymbols c =
    List.sort <| List.map Tuple.first c


{-| It gives the propositional symbols that take place in the clause

    csplSymbols cs1 =
        [ "p", "q", "r" ]

-}
csplSymbols : ClausePLSet -> List PSymb
csplSymbols cs =
    List.sort <| List.foldl (\c ac -> uniqueConcatList ac (cplSymbols c)) [] cs


{-| It gives all possible interpretations for a clause

    cplInterpretations c1 == [ [], [ "p" ], [ "p", "q" ], [ "p", "q", "r" ], [ "p", "r" ], [ "q" ], [ "q", "r" ], [ "r" ] ]

    cplInterpretation c2 == [ [], [ "p" ], [ "p", "r" ], [ "r" ] ]

-}
cplInterpretations : ClausePL -> List Interpretation
cplInterpretations c =
    List.sort <| powerset <| cplSymbols c


{-| It gives all possible interpretations for a set of clauses

    csplInterpretations cs1 == [ [], [ "p" ], [ "p", "q" ], [ "p", "q", "r" ], [ "p", "r" ], [ "q" ], [ "q", "r" ], [ "r" ] ]

    csplInterpretations [ [ Atom "p" ], [ Atom "q" ] ] == [ [], [ "p" ], [ "p", "q" ], [ "q" ] ]

-}
csplInterpretations : ClausePLSet -> List Interpretation
csplInterpretations cs =
    List.sort <| powerset <| csplSymbols cs


{-| It converts a ClausePLLiteral to a Literal (FormulaPL)
-}
clauseLitToLiteral : ClausePLLiteral -> Literal
clauseLitToLiteral ( symb, sign ) =
    if sign then
        Atom symb

    else
        Neg (Atom symb)


{-| It evaluates the truth value of the clause regarding to a interpretation

    cplValuation c2 [ "p", "r" ] == True

    cplValuation c2 [] == True

    cplValuation c2 [ "p" ] == False

-}
cplValuation : ClausePL -> Interpretation -> Bool
cplValuation c i =
    List.any
        (\( symb, sign ) ->
            if sign then
                List.member symb i

            else
                not <| List.member symb i
        )
        c


{-| It evaluates the truth value of a set of clauses regarding to a interpretation

    csplValuation cs1 [ "r" ] == True

    csplValuation cs1 [] == False

-}
csplValuation : ClausePLSet -> Interpretation -> Bool
csplValuation cs i =
    List.all (\c -> cplValuation c i) cs


{-| It generates all models of a clause by bruteforce, valuating the truth value for each interpretation

    plModels c1 == [ [], [ "p" ], [ "p", "q", "r" ], [ "p", "r" ], [ "q" ], [ "q", "r" ], [ "r" ] ]

    cplModels c2 == [ [], [ "p", "r" ], [ "r" ] ]

    cplModels c3 == [ [ ( "r", True ) ] ]

-}
cplModels : ClausePL -> List Interpretation
cplModels c =
    List.filter (\i -> cplValuation c i) <| cplInterpretations c


{-| It generates all models of a set of clauses by bruteforce, valuating the truth value for each interpretation

    csplModels cs1 == [ [ "p", "q", "r" ], [ "p", "r" ], [ "q", "r" ], [ "r" ] ]

-}
csplModels : ClausePLSet -> List Interpretation
csplModels cs =
    List.filter (\i -> csplValuation cs i) <| csplInterpretations cs


{-| It checks if a clause is unsatisfible, that is if it is empty.

    cplIsInsat c1 == False

    cplIsInsat c2 == False

    cplIsInsat [] == True

-}
cplIsInsat : ClausePL -> Bool
cplIsInsat c =
    List.isEmpty c


{-| It checks if a set of clauses is a tautology, that is if all clauses are tautologies.

    csplIsTaut cs1 == False

    csplIsTaut (List.map (\x -> x ++ [ ( "r", False ) ]) cs1) == True

-}
csplIsTaut : ClausePLSet -> Bool
csplIsTaut cs =
    List.all (\c -> cplIsTautology c) cs


{-| It checks if a set of clauses is satisfiable by bruteforce, calculating its models and checking any exists

    csplIsSat cs1 == True

    csplIsSat (cs1 ++ [ ( "r", False ) ]) == False

-}
csplIsSat : ClausePLSet -> Bool
csplIsSat cs =
    not <| List.isEmpty <| csplModels cs


{-| It checks if a set of clauses are satisfiable by brute force, calculates its models and verifies that none exist.
-}
csplIsInsat : ClausePLSet -> Bool
csplIsInsat cs =
    List.isEmpty <| csplModels cs



-- From formulas to clauses


{-| It pass a CNF formula to a Set of clausses
-}
csplFromCNF : FormulaPL -> Maybe ClausePLSet
csplFromCNF f =
    let
        toClauseLit l =
            case l of
                Atom symb ->
                    Just ( symb, True )

                Neg (Atom symb) ->
                    Just ( symb, False )

                _ ->
                    Nothing
    in
    PL_NF.cnfAsLiteralSets f
        |> Maybe.map (List.map (cplSort << List.filterMap toClauseLit))


{-| Express a formula as a set of clauses with the same models, through its conjunctive normal form (it may grow exponentially; see `fplToClausesTseitin` for a linear alternative).

    f1 = fplRead "¬p & q <-> r"
    fplToClauses f1 == [[("p",True),("r",True),("q",False)],[("p",False),("r",False)],[("q",True),("r",False)]]

-}
fplToClauses : FormulaPL -> ClausePLSet
fplToClauses f =
    csplRemoveTautClauses <| csplRemoveSubsumedClauses <| Maybe.withDefault [ [] ] <| csplFromCNF <| PL_NF.fplToCNF f


{-| Express a set of formulas as a set of clauses with the same models, through the conjunctive normal form of each formula.

    fs = List.map fplRead ["p->q", "p | q -> r", "¬p | q"]
    splToClauses fs == [[("q",True),("p",False)],[("r",True),("p",False)],[("r",True),("q",False)]]

-}
splToClauses : SetPL -> ClausePLSet
splToClauses fs =
    csplRemoveTautClauses <| csplRemoveSubsumedClauses <| List.concat <| List.map fplToClauses fs


{-| Express a formula as a set of clauses through the Tseitin transformation (see `LogicUS.PL.NormalForms.splToCNFTseitin`). The result is _equisatisfiable_ with the formula, not equivalent: it uses fresh symbols `𝜏ᵢ`, but its size is linear in the size of the formula.
-}
fplToClausesTseitin : FormulaPL -> ClausePLSet
fplToClausesTseitin f =
    splToClausesTseitin [ f ]


{-| Express a set of formulas as a set of clauses through the Tseitin transformation. The fresh symbols `𝜏ᵢ` are shared by the whole set, so the result is equisatisfiable with the set.
-}
splToClausesTseitin : SetPL -> ClausePLSet
splToClausesTseitin fs =
    csplRemoveTautClauses <| Maybe.withDefault [ [] ] <| csplFromCNF <| PL_NF.splToCNFTseitin fs



--===========--
--  PARSER   --
--===========--

{-| It reads the formula from a string. It returns a clause (if it can be read it) and the empty clause (if not).
-}
cplRead : String -> ClausePL
cplRead = (cplReadExtraction  << cplReadFromString)

{-| It reads the formula from a string. It returns a tuple with may be a formula (if it can be read it) and a message of error it it cannot.

    cplReadFromString "p_{1}, p_{2}, ¬q_{1}, q_{2}" == (Just [("p_{1}",True),("p_{2}",True),("q_{1}",False),("q_{2}",True)],"","")

    cplReadFromString "{p_{1}, p_{2}, ¬q_{1}, q_{2}}" == (Just [("p_{1}",True),("p_{2}",True),("q_{1}",False),("q_{2}",True)],"",""

    cplReadFromString "{p_{1}, p_{2}, ¬q_{1}, q_{2}" == (Nothing,"{p_{1},p_{2},¬q_{1},q_{2}","Error: [{ col = 26, problem = Expecting ',', row = 1 },{ col = 26, problem = Expecting '}', row = 1 }]")

    cplReadFromString "{}" == ( Just [], "", "" )

    cplReadFromString "" == ( Nothing, "", "Argument is empty" )

-}
cplReadFromString : String -> ( Maybe ClausePL, String, String )
cplReadFromString x =
    let
        clean_x =
            cleanSpaces x
    in
    case String.left 1 <| clean_x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        "{" ->
            case Parser.run cplParser clean_x of
                Ok y ->
                    ( Maybe.Just (cplSort (uniqueConcatList [] y)), "", "" )

                Err y ->
                    ( Maybe.Nothing, clean_x, parserErrorToString clean_x 0 y )

        _ ->
            case Parser.run cplParser ("{" ++ clean_x ++ "}") of
                Ok y ->
                    ( Maybe.Just (cplSort (uniqueConcatList [] y)), "", "" )

                Err y ->
                    ( Maybe.Nothing, "{" ++ clean_x ++ "}", parserErrorToString ("{" ++ clean_x ++ "}") 1 y )


{-| It extracts the clause readed. If it is Nothing then it returns an empty clause

    (cplReadExtraction << cplReadFromString) "p_{1}, p_{2}, ¬q_{1}, q_{2}" == [ ( "p_{1}", True ), ( "p_{2}", True ), ( "q_{1}", False ), ( "q_{2}", True ) ]

    (cplReadExtraction << cplReadFromString) "{p_{1}, p_{2}, ¬q_{1}, q_{2}" == []

    (cplReadExtraction << cplReadFromString) "{}" == []

-}
cplReadExtraction : ( Maybe ClausePL, String, String ) -> ClausePL
cplReadExtraction ( c, _, _ ) =
    cplSort <| Maybe.withDefault [] c


{-| It gives the corresponding input syntax of a clause

    cplToInputString c1 = "{¬p,¬q,r}"

    cplToInputString c3 == "{r}"

-}
cplToInputString : ClausePL -> String
cplToInputString c =
    case c of
        [] ->
            "{}"

        _ ->
            "{" ++ (String.join "," <| List.map (PL_SS.fplToInputString << clauseLitToLiteral) <| cplSort c) ++ "}"



--- Parser Builder Functions
-- It defines the syntax of a propositional variable that can be subscripting or not


plVarNameParser : Parser String
plVarNameParser =
    Parser.succeed ()
        |. Parser.chompIf Char.isLower
        |. Parser.chompWhile Char.isLower
        |> Parser.getChompedString


plVarParser : Parser ( String, List Int )
plVarParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable plVarIdentifierSubindexedParser
        , Parser.succeed (\x -> ( x, [] ))
            |= plVarNameParser
        ]


plVarIdentifierSubindexedParser : Parser ( String, List Int )
plVarIdentifierSubindexedParser =
    Parser.succeed Tuple.pair
        |= plVarNameParser
        |= Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Parser.int
            , trailing = Forbidden
            }


cplParser : Parser ClausePL
cplParser =
    Parser.succeed identity
        |= cplParserAux
        |. Parser.end


cplParserAux : Parser ClausePL
cplParserAux =
    Parser.sequence
        { start = "{"
        , separator = ","
        , end = "}"
        , spaces = Parser.spaces
        , item = literalParser
        , trailing = Optional
        }


literalParser : Parser ClausePLLiteral
literalParser =
    Parser.oneOf
        [ Parser.succeed (\x -> ( x, False ))
            |. Parser.oneOf
                [ Parser.symbol "¬"
                , Parser.symbol "-"
                ]
            |= plVarParser
        , Parser.succeed (\x -> ( x, True ))
            |= plVarParser
        ]



--================--
-- REPRESENTATION --
--================--


{-| It generates the String representation of a ClausePL using unicode symbols.

    cplToString c1 == "{¬ p, ¬ q, r}"

-}
cplToString : ClausePL -> String
cplToString c =
    if List.isEmpty c then
        "□"

    else
        "{" ++ (String.join "," <| List.map (PL_SS.fplToString << clauseLitToLiteral) <| cplSort c) ++ "}"


{-| It generates the Latex string of a ClausePL. The result requires a math enviroment to be displayed.

    cplToMathString c1 == "\\lbrace \\neg p, \\neg q, r\\rbrace"

-}
cplToMathString : ClausePL -> String
cplToMathString c =
    if List.isEmpty c then
        "\\Box"

    else
        "\\{" ++ (String.join "," <| List.map (PL_SS.fplToMathString << clauseLitToLiteral) <| cplSort c) ++ "\\}"


{-| It generates the String representation of a Set of Clauses using unicode symbols.

    csplToString cs == "{{¬ p, q},{¬ p, r},{¬ q, r}}"

-}
csplToString : ClausePLSet -> String
csplToString cs =
    "{" ++ (String.join "," <| List.map (cplToString << cplSort) cs) ++ "}"


{-| It generates the Latex string of a Set of Clauses. The result requires a math enviroment to be displayed.

    csplToMathString cs == "\\lbrace\\lbrace \\neg p, q\\rbrace, \\, \\lbrace \\neg p, r\\rbrace, \\, \\lbrace \\neg q, r\\rbrace\\rbrace"

-}
csplToMathString : ClausePLSet -> String
csplToMathString cs =
    "\\lbrace" ++ (String.join ", \\, " <| List.map (\x -> (cplToMathString << cplSort) x) cs) ++ "\\rbrace"


{-| It generates the representation of a set of clauses following DIMACS format.
-}
csplToDIMACS : ClausePLSet -> ( String, Dict Int PSymb )
csplToDIMACS cs =
    let
        symbs =
            Dict.fromList <| List.indexedMap (\i s -> ( s, i + 1 )) <| csplSymbols cs
    in
    let
        cplToDIMACS c =
            (String.join " " <|
                List.map
                    (\( symb, sign ) ->
                        let
                            symb_id =
                                Maybe.withDefault 0 <| Dict.get symb symbs
                        in
                        if sign then
                            String.fromInt symb_id

                        else
                            String.fromInt <| -symb_id
                    )
                    c
            )
                ++ " 0"

        symbsStr =
            String.join ", " <| List.map (\( k, v ) -> String.fromInt v ++ " : " ++ (PL_SS.fplToMathString <| PL_SS.Atom k)) <| Dict.toList symbs
    in
    ( "p cnf " ++ (String.fromInt <| Dict.size symbs) ++ " " ++ (String.fromInt <| List.length cs) ++ "\n" ++ (String.join "\n" <| List.map cplToDIMACS cs) ++ "\nc " ++ symbsStr
    , Dict.fromList <| List.map2 Tuple.pair (Dict.values symbs) (Dict.keys symbs)
    )

