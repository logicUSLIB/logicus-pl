module LogicUS.PL.CSP exposing
    ( BigFPL(..), bfplReadFromString, bfplReadExtraction, bfplRead
    , bfplToFPL, sbfplToSPL
    , sbfplsolver, solver
    , bfplToString, bfplToMathString, bfplToMathString2, solutionModelToString, solutionModelToMathString
    )

{-| This module is designed for working with Constraint Satisfaction Problems, defining it by Big Formulas using Big Operators. For this purpose this module provides a parser, for reading a big formula directly from a String, a transformer from BigFormulas to standard FormulaPL, a SAT Solver (inspired in Chronological Backtracking + MRV) and the functions for representing the big formulas in string (raw) and in Latex format.


# Defining BigFPL

@docs BigFPL, bfplReadFromString, bfplReadExtraction, bfplRead


# BigFPL to FormulaPL

@docs bfplToFPL, sbfplToSPL


# CSP Solver

@docs sbfplsolver, solver


# Representation

@docs bfplToString, bfplToMathString, bfplToMathString2, solutionModelToString, solutionModelToMathString

-}

import Dict exposing (Dict)
import List.Extra as LE
import LogicUS.PL.A_Expressions as Aux_AE exposing (A_Expr)
import LogicUS.PL.AuxiliarFunctions exposing (parserErrorToString, uniqueConcatList)
import LogicUS.PL.B_Expressions as Aux_BE exposing (B_Expr)
import LogicUS.PL.Clauses as PL_CL exposing (ClausePL, ClausePLSet, fplToClauses)
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL, Interpretation, PSymb)
import Maybe.Extra as ME
import Parser exposing ((|.), (|=), Parser, Trailing(..))
import Set



-- The type of a Paramifier variable


type alias Param =
    { name : String
    , values : List Int
    }


{-| It defines the structure of a BigFPL Formula
-}
type BigFPL
    = Atom String (List A_Expr)
    | Neg BigFPL
    | Conj BigFPL BigFPL
    | Disj BigFPL BigFPL
    | Impl BigFPL BigFPL
    | Equi BigFPL BigFPL
    | BAnd (List Param) B_Expr BigFPL
    | BOr (List Param) B_Expr BigFPL
    | Insat
    | Taut



------------
-- PARSER --
------------


atomName : Parser String
atomName =
    Parser.variable
        { start = Char.isAlpha
        , inner = \c -> Char.isAlpha c
        , reserved = Set.fromList []
        }


atomSubscript : Parser BigFPL
atomSubscript =
    Parser.succeed Atom
        |= atomName
        |= Parser.sequence
            { start = "_{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item = Aux_AE.expressionA
            , trailing = Forbidden
            }


atomParser : Parser BigFPL
atomParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable atomSubscript
        , Parser.succeed (\x -> Atom x [])
            |= atomName
        ]


nameParamBigFPL : Parser String
nameParamBigFPL =
    Parser.succeed identity
        |. Parser.chompIf Char.isLower
        |. Parser.chompWhile Char.isLower
        |. Parser.chompWhile Char.isDigit
        |> Parser.getChompedString


myInt : Parser Int
myInt =
    Parser.andThen myIntToInt
        (Parser.succeed identity
            |. Parser.chompWhile Char.isDigit
            |> Parser.getChompedString
        )


myIntToInt : String -> Parser Int
myIntToInt readed =
    case Parser.run Parser.int readed of
        Ok i ->
            Parser.succeed i

        Err _ ->
            Parser.problem "Expecting Int"


valuesParamBigFPL : Parser (List Int)
valuesParamBigFPL =
    Parser.oneOf
        [ Parser.sequence
            { start = "{"
            , separator = ","
            , end = "}"
            , spaces = Parser.spaces
            , item =
                Parser.oneOf
                    [ Parser.succeed negate
                        |. Parser.symbol "-"
                        |= myInt
                    , myInt
                    ]
            , trailing = Optional
            }
        , Parser.succeed List.range
            |. Parser.symbol "("
            |= Parser.oneOf
                [ Parser.succeed negate
                    |. Parser.symbol "-"
                    |= myInt
                , myInt
                ]
            |. Parser.symbol ".."
            |= Parser.oneOf
                [ Parser.succeed negate
                    |. Parser.symbol "-"
                    |= myInt
                , myInt
                ]
            |. Parser.symbol ")"
        ]


paramBigFPL : Parser Param
paramBigFPL =
    Parser.succeed (\n v -> { name = n, values = v })
        |= nameParamBigFPL
        |. Parser.symbol "\\in"
        |= valuesParamBigFPL


listParamBigFPL : Parser (List Param)
listParamBigFPL =
    Parser.sequence
        { start = ""
        , separator = ","
        , end = ""
        , spaces = Parser.spaces
        , item = paramBigFPL
        , trailing = Forbidden
        }


termBigFPL : Parser BigFPL
termBigFPL =
    Parser.oneOf
        [ Parser.succeed identity
            |= atomParser
        , Parser.succeed BAnd
            |. Parser.oneOf
                [ Parser.symbol "/\\"
                , Parser.symbol "!&"
                , Parser.symbol "⋀"
                ]
            |. Parser.symbol "_{"
            |= listParamBigFPL
            |= Parser.oneOf
                [ Parser.succeed identity
                    |. Parser.symbol ":"
                    |= Aux_BE.expressionB
                , Parser.succeed Aux_BE.T
                ]
            |. Parser.symbol "}"
            |. Parser.symbol "("
            |= Parser.lazy (\_ -> expressionBigFPL)
            |. Parser.symbol ")"
        , Parser.succeed BOr
            |. Parser.oneOf
                [ Parser.symbol "\\/"
                , Parser.symbol "!|"
                , Parser.symbol "⋁"
                ]
            |. Parser.symbol "_{"
            |= listParamBigFPL
            |= Parser.oneOf
                [ Parser.succeed identity
                    |. Parser.symbol ":"
                    |= Aux_BE.expressionB
                , Parser.succeed Aux_BE.T
                ]
            |. Parser.symbol "}"
            |. Parser.symbol "("
            |= Parser.lazy (\_ -> expressionBigFPL)
            |. Parser.symbol ")"
        , Parser.succeed identity
            |. Parser.symbol "("
            |= Parser.lazy (\_ -> expressionBigFPL)
            |. Parser.symbol ")"
        , Parser.succeed Neg
            |. Parser.oneOf
                [ Parser.symbol "¬"
                , Parser.symbol "-"
                ]
            |= Parser.lazy (\_ -> termBigFPL)
        , Parser.succeed
            Insat
            |. Parser.symbol "!F"
        , Parser.succeed Taut
            |. Parser.symbol "!T"
        ]


expressionBigFPL : Parser BigFPL
expressionBigFPL =
    termBigFPL |> Parser.andThen (expressionBigFPLAux [])


type Operator
    = AndOp
    | OrOp
    | ImplOp
    | EquivOp


operator : Parser Operator
operator =
    Parser.oneOf
        [ Parser.succeed AndOp
            |. Parser.symbol "&"
        , Parser.succeed AndOp
            |. Parser.symbol "∧"
        , Parser.succeed OrOp
            |. Parser.symbol "|"
        , Parser.succeed OrOp
            |. Parser.symbol "∨"
        , Parser.succeed ImplOp
            |. Parser.symbol "->"
        , Parser.succeed ImplOp
            |. Parser.symbol "→"
        , Parser.succeed EquivOp
            |. Parser.symbol "<->"
        , Parser.succeed EquivOp
            |. Parser.symbol "↔"
        ]


expressionBigFPLAux : List ( BigFPL, Operator ) -> BigFPL -> Parser BigFPL
expressionBigFPLAux revOps expr =
    Parser.oneOf
        [ Parser.succeed Tuple.pair
            |= operator
            |= termBigFPL
            |> Parser.andThen (\( op, newExpr ) -> expressionBigFPLAux (( expr, op ) :: revOps) newExpr)
        , Parser.lazy (\_ -> Parser.succeed (finalize revOps expr))
        ]


finalize : List ( BigFPL, Operator ) -> BigFPL -> BigFPL
finalize revOps finalExpr =
    case revOps of
        [] ->
            finalExpr

        -- AND EXPRESSIONS CASES
        -- And operation have the maximum priorty, so module have a unique case
        ( expr, AndOp ) :: otherRevOps ->
            finalize otherRevOps (Conj expr finalExpr)

        -- OR EXPRESSIONS CASES
        -- Or have the second maximum priority, so we need to determine how parser's going to do if it searches an and after, and if it searches something different.
        ( expr, OrOp ) :: ( expr2, AndOp ) :: otherRevOps ->
            Disj (finalize (( expr2, AndOp ) :: otherRevOps) expr) finalExpr

        ( expr, OrOp ) :: otherRevOps ->
            finalize otherRevOps (Disj expr finalExpr)

        -- IMPLICATION EXPRESSIONS CASES
        ( expr, ImplOp ) :: ( expr2, AndOp ) :: otherRevOps ->
            Impl (finalize (( expr2, AndOp ) :: otherRevOps) expr) finalExpr

        ( expr, ImplOp ) :: ( expr2, OrOp ) :: otherRevOps ->
            Impl (finalize (( expr2, OrOp ) :: otherRevOps) expr) finalExpr

        ( expr, ImplOp ) :: otherRevOps ->
            finalize otherRevOps (Impl expr finalExpr)

        -- EQUIVALATION EXPRESSIONS CASES
        ( expr, EquivOp ) :: ( expr2, AndOp ) :: otherRevOps ->
            Equi (finalize (( expr2, AndOp ) :: otherRevOps) expr) finalExpr

        ( expr, EquivOp ) :: ( expr2, OrOp ) :: otherRevOps ->
            Equi (finalize (( expr2, OrOp ) :: otherRevOps) expr) finalExpr

        ( expr, EquivOp ) :: ( expr2, ImplOp ) :: otherRevOps ->
            Equi (finalize (( expr2, ImplOp ) :: otherRevOps) expr) finalExpr

        ( expr, EquivOp ) :: otherRevOps ->
            finalize otherRevOps (Equi expr finalExpr)


{-| It allows defining BFPL from text strings, through a parser. If the BFPL parser fails, then it gives Insat
-}
bfplRead : String -> BigFPL
bfplRead = (bfplReadExtraction << bfplReadFromString)

{-| It allows defining BFPL from text strings, through a parser. To do this, a series of rules are established:

  - Atomic formulas (propositional variables) correspond to propositional variables, made up of text strings, with uppercase characters, and can optionally be sub-indexed by a series of indices that correspond to arithmetic expressions. Said indices are specified between the symbols `_{` and `}`; and separated by commas. Examples of atomic formulas are: `P`,`Q_{i, j}`,`AL_{i + k, i-k}`.

  - An arithmetic expression can correspond to an integer, to a variable specified as a string of characters in lowercase followed, optionally, by some numeric digits (x, i1, y33), or the binary combination of two arithmetic expressions through the infix operators: + (sum), - (subtraction), \* (product), // (integer division),% (modulus).

  - The formulas can be defined as atomic formulas or as associations of them through infix binary connectives: `&` (conjunction), `|` (disjubation), `->` (implication), `<->` (equivalence ); the unitary connective: `¬` (negation); or two big connectives that follow the format: BigOp + PARAMETERS + CONDITION + BigFPL
      - The BigOp can correspond to `!&` (BigAnd) or `!|` (BigOr).

      - The list of parameters that establishes associations between the parameter's Paramifier and its variation universe in the form `Paramifier {universe}` or `Paramifier (universe)` (according to the cases described below). These associations are enclosed in brackets `[`, `]`, and separated by commas. Note that, for example, `!& [I (1..8), j (1..8)] {T} (...)` would be equivalent to `!& [I (1..8) ] {T}!& [J (1..8)] {T} (....)`

      - The universe of variation of a parameter can be specified through discrete integer values, expressed between braces and separated by commas, for example `i {1,2,3,4,5,6,7,8}`; Or as a range expressed as `(ll:up)` in the way `ll` corresponds to the lower limit, and`ul` to the upper limit, both included in the range, equivalent to the previous example `i (1:8)`

      - The condition is established from a Boolean expression expressed between braces and that can correspond to: the true condition `T`, the false expression`F`, a comparison between arithmetic expressions (in which parameters defined in the operator itself or in predecessor, more external operators). These comparative expressions are expressed in brackets and can correspond to the comparative ones: `=` (equal), `!=` (Different), `> =` (greater or equal), `<=` (less or equal), `>`(major strict),`<`(minor strict); Or with Boolean expressions created from Boolean operators `AND`,`OR`, `NOT`.

As a final example, the restriction of the absence of two queens on the same secondary diagonal, in the 8 Queens problem, could be expressed as:

`!& [i (0:7), j (0:7)] {T} (P_{i, j} ->!& [k (-7:7)] {[k!= 0] AND [i + k> = 0] AND [j-k> = 0] AND [i + k <= 7] AND [j-k <= 7]} (¬P_{i + k, j-k}))`

-}
bfplReadFromString : String -> ( Maybe BigFPL, String )
bfplReadFromString str =
    if str == "" then
        ( Nothing, "Empty expression" )

    else
        case Parser.run expressionBigFPL <| String.replace " " "" <| String.replace "\n" "" <| "(" ++ str ++ ")" of
            Ok y ->
                if isWFF y then
                    ( Just y, "" )

                else
                    ( Nothing, "Illegal use of indices" )

            Err err ->
                ( Nothing, parserErrorToString (String.replace " " "" <| String.replace "\n" "" <| "(" ++ str ++ ")") 1 err )


{-| It allows to extract the formula readed. If there is a parsing error, then it returns Insat formula
-}
bfplReadExtraction : ( Maybe BigFPL, String ) -> BigFPL
bfplReadExtraction ( f, _ ) =
    Maybe.withDefault Insat f



-- It checks if the formula is well formed.


isWFF : BigFPL -> Bool
isWFF f =
    case f of
        Atom _ [] ->
            True

        Atom _ _ ->
            False

        Neg p ->
            isWFF p

        Conj p q ->
            isWFF p && isWFF q

        Disj p q ->
            isWFF p && isWFF q

        Impl p q ->
            isWFF p && isWFF q

        Equi p q ->
            isWFF p && isWFF q

        BAnd li c p ->
            let
                new_curli =
                    List.map .name li
            in
            if LE.allDifferent new_curli && List.all (\x -> List.member x new_curli) (Aux_BE.varsInB_Expr c) then
                isWFFAux p new_curli

            else
                False

        BOr li c p ->
            let
                new_curli =
                    List.map .name li
            in
            if LE.allDifferent new_curli && List.all (\x -> List.member x new_curli) (Aux_BE.varsInB_Expr c) then
                isWFFAux p new_curli

            else
                False

        Insat ->
            True

        Taut ->
            True


isWFFAux : BigFPL -> List String -> Bool
isWFFAux f curli =
    case f of
        Atom _ is ->
            List.all (\x -> List.member x curli) <|
                List.foldl (\i ac -> uniqueConcatList ac <| Aux_AE.varsInA_Expr i) [] is

        Neg p ->
            isWFFAux p curli

        Conj p q ->
            isWFFAux p curli && isWFFAux q curli

        Disj p q ->
            isWFFAux p curli && isWFFAux q curli

        Impl p q ->
            isWFFAux p curli && isWFFAux q curli

        Equi p q ->
            isWFFAux p curli && isWFFAux q curli

        BAnd li c p ->
            let
                new_curli =
                    curli ++ List.map .name li
            in
            if LE.allDifferent new_curli && List.all (\x -> List.member x new_curli) (Aux_BE.varsInB_Expr c) then
                isWFFAux p new_curli

            else
                False

        BOr li c p ->
            let
                new_curli =
                    curli ++ List.map .name li
            in
            if LE.allDifferent new_curli && List.all (\x -> List.member x new_curli) (Aux_BE.varsInB_Expr c) then
                isWFFAux p new_curli

            else
                False

        Insat ->
            True

        Taut ->
            True



-- EXPANSION
-- It pass a bfpl formula to a fpl evaluating the diferent posibles values.


bfplExpansionAux : Dict String Int -> BigFPL -> Maybe FormulaPL
bfplExpansionAux var_val f =
    case f of
        Atom p is ->
            Maybe.map (PL_SS.Atom << Tuple.pair p) <| ME.combine (List.map (\i -> Aux_AE.evaluateAExpr i var_val) is)

        Neg p ->
            Maybe.map PL_SS.Neg (bfplExpansionAux var_val p)

        Conj p q ->
            Maybe.map2 PL_SS.Conj (bfplExpansionAux var_val p) (bfplExpansionAux var_val q)

        Disj p q ->
            Maybe.map2 PL_SS.Disj (bfplExpansionAux var_val p) (bfplExpansionAux var_val q)

        Impl p q ->
            Maybe.map2 PL_SS.Impl (bfplExpansionAux var_val p) (bfplExpansionAux var_val q)

        Equi p q ->
            Maybe.map2 PL_SS.Equi (bfplExpansionAux var_val p) (bfplExpansionAux var_val q)

        BAnd li c p ->
            let
                names =
                    List.map .name li

                values =
                    List.map .values li
            in
            let
                valid_subs =
                    List.filter (\s -> Maybe.withDefault False <| Aux_BE.evaluateBExpr c s) <| List.map (\x -> Dict.union var_val <| Dict.fromList <| LE.zip names x) <| LE.cartesianProduct <| values
            in
            Maybe.map PL_SS.splConjunction <| ME.combine <| List.map (\s -> bfplExpansionAux s p) valid_subs

        BOr li c p ->
            let
                names =
                    List.map .name li

                values =
                    List.map .values li
            in
            let
                valid_subs =
                    List.filter (\s -> Maybe.withDefault False <| Aux_BE.evaluateBExpr c s) <| List.map (\x -> Dict.union var_val <| Dict.fromList <| LE.zip names x) <| LE.cartesianProduct <| values
            in
            Maybe.map PL_SS.splDisjunction <| ME.combine <| List.map (\s -> bfplExpansionAux s p) valid_subs

        Insat ->
            Just PL_SS.Insat

        Taut ->
            Just PL_SS.Taut


{-| It converts a BigFPL to a FPL
-}
bfplToFPL : BigFPL -> FormulaPL
bfplToFPL f =
    if isWFF f then
        Maybe.withDefault PL_SS.Insat <| bfplExpansionAux Dict.empty <| f

    else
        PL_SS.Insat


{-| It converts a BigFPL to a FPL
-}
sbfplToSPL : List BigFPL -> PL_SS.SetPL
sbfplToSPL ls =
    uniqueConcatList [] <| List.map bfplToFPL ls



-- SAT SOLVER
-- Get vars that take place in a set of clauses counting how many times it appears in positive and negative literals.


varsClauses : ClausePLSet -> Dict PSymb ( Int, Int )
varsClauses cs =
    List.foldl
        (\( ( a, s ), c ) ac ->
            case Dict.get a ac of
                Just ( pc, nc ) ->
                    if s then
                        Dict.insert a ( pc + c, nc ) ac

                    else
                        Dict.insert a ( pc, nc + c ) ac

                _ ->
                    if s then
                        Dict.insert a ( c, 0 ) ac

                    else
                        Dict.insert a ( 0, c ) ac
        )
        Dict.empty
        (List.map (\( l, xs ) -> ( l, List.length xs + 1 )) <| LE.gatherEquals <| List.concat <| cs)



-- It get the literals that appears in unitary clauses in a set of clauses


getVarsUnitaryClauses : List ClausePL -> List ( PSymb, Bool )
getVarsUnitaryClauses cls =
    List.foldl
        (\c ac ->
            if List.length c == 1 then
                ac ++ c

            else
                ac
        )
        []
        cls



-- It updates, at the same time, the set of available vars and the set of remaining (not satified) clauses in the search process


updationAvailable : List ( PSymb, Bool ) -> Dict PSymb ( Int, Int ) -> List ClausePL -> ( Dict PSymb ( Int, Int ), List ClausePL )
updationAvailable used_vars cur_av_vars cur_cls =
    List.foldl
        (\c ( ac1, ac2 ) ->
            if List.any (\l -> List.member l used_vars) c then
                ( Dict.map
                    (\a ( pc, nc ) ->
                        if List.member ( a, True ) c then
                            ( pc - 1, nc )

                        else if List.member ( a, False ) c then
                            ( pc, nc - 1 )

                        else
                            ( pc, nc )
                    )
                    ac1
                , ac2
                )

            else
                ( ac1, ac2 ++ [ List.filter (\( a, s ) -> not <| List.member ( a, not s ) used_vars) c ] )
        )
        ( List.foldl (\( a, _ ) ac -> Dict.remove a ac) cur_av_vars used_vars, [] )
        cur_cls



-- It performances the search process as a chronological backtracking using MRV heuristic


solverAux : List PSymb -> Dict PSymb ( Int, Int ) -> List ClausePL -> Maybe (List PSymb)
solverAux asig av_vars cls =
    if List.member [] cls then
        Nothing

    else
        case getVarsUnitaryClauses cls of
            x :: _ ->
                -- Propagate one unit literal at a time: propagating {p} and {¬p} together
                -- would mark both clauses as satisfied and miss the conflict.
                let
                    new_asig =
                        if Tuple.second x then
                            asig ++ [ Tuple.first x ]

                        else
                            asig

                    ( new_av_vars, new_cls ) =
                        updationAvailable [ x ] av_vars cls
                in
                solverAux new_asig new_av_vars new_cls

            [] ->
                let
                    best_var =
                        LE.maximumBy (\( _, ( pc, nc ) ) -> pc + nc) <|
                            List.filter (\( _, ( pc, nc ) ) -> pc + nc > 0) <|
                                Dict.toList av_vars
                in
                case best_var of
                    Just ( bv, ( pc, nc ) ) ->
                        let
                            new_asig1 =
                                asig ++ [ bv ]

                            ( new_av_vars1, new_cls1 ) =
                                updationAvailable [ ( bv, True ) ] av_vars cls

                            ( new_av_vars2, new_cls2 ) =
                                updationAvailable [ ( bv, False ) ] av_vars cls
                        in
                        if nc > pc then
                            ME.or (solverAux asig new_av_vars2 new_cls2) (solverAux new_asig1 new_av_vars1 new_cls1)

                        else
                            ME.or (solverAux new_asig1 new_av_vars1 new_cls1) (solverAux asig new_av_vars2 new_cls2)

                    Nothing ->
                        case cls of
                            [] ->
                                Just asig

                            (( v, _ ) :: _) :: _ ->
                                -- Defensive: a clause is still pending although no counted variable is left.
                                ME.or
                                    (solverAux (asig ++ [ v ]) (Dict.remove v av_vars) (Tuple.second (updationAvailable [ ( v, True ) ] av_vars cls)))
                                    (solverAux asig (Dict.remove v av_vars) (Tuple.second (updationAvailable [ ( v, False ) ] av_vars cls)))

                            _ ->
                                Nothing


{-| It allows resolve the satisfiability of a set of BigFormulas using Backtracking + MRV
-}
sbfplsolver : List BigFPL -> ( Bool, List PSymb )
sbfplsolver fs =
    let
        cls =
            PL_CL.csplRemoveSubsumedClauses <| List.concat <| List.map (fplToClauses << bfplToFPL) fs
    in
    case solverAux [] (varsClauses cls) cls of
        Nothing ->
            ( False, [] )

        Just y ->
            ( True, y )


{-| It allows resolve the satisfiability of a set of clauses using Backtracking + MRV
-}
solver : List ClausePL -> ( Bool, List PSymb )
solver cls =
    case solverAux [] (varsClauses cls) cls of
        Nothing ->
            ( False, [] )

        Just y ->
            ( True, y )



-- Representation
-- It generates the string of a parameter Param


paramToString : Param -> String
paramToString i =
    i.name ++ ":" ++ "{" ++ (String.join "," <| List.map String.fromInt i.values) ++ "}"



-- It generates the string of a parameter Param in latex format


paramToMathString : Param -> String
paramToMathString i =
    i.name ++ "\\in \\{" ++ (Maybe.withDefault "" <| Maybe.map String.fromInt <| List.head i.values) ++ ".." ++ (Maybe.withDefault "" <| Maybe.map String.fromInt <| LE.last i.values) ++ "\\}"


{-| It generates the String representation of a BigFPL formula.
-}
bfplToString : BigFPL -> String
bfplToString f =
    case f of
        Atom pname is ->
            pname ++ "_{" ++ (String.join "," <| List.map Aux_AE.toStringAExpr is) ++ "}"

        Neg p ->
            "¬ " ++ bfplToString p

        Conj p q ->
            "( " ++ bfplToString p ++ " ∧ " ++ bfplToString q ++ " )"

        Disj p q ->
            "( " ++ bfplToString p ++ " ∨ " ++ bfplToString q ++ " )"

        Impl p q ->
            "( " ++ bfplToString p ++ " → " ++ bfplToString q ++ " )"

        Equi p q ->
            "( " ++ bfplToString p ++ " ↔ " ++ bfplToString q ++ " )"

        Insat ->
            "⊥"

        Taut ->
            "⊤"

        BAnd li c p ->
            "⋀[" ++ (String.join ", " <| List.map paramToString li) ++ "]" ++ "{" ++ Aux_BE.toStringBExpr c ++ "} " ++ bfplToString p

        BOr li c p ->
            "⋁[" ++ (String.join ", " <| List.map paramToString li) ++ "]" ++ "{" ++ Aux_BE.toStringBExpr c ++ "} " ++ bfplToString p


{-| It generates the String representation of a BigFPL formula in Latex Format
-}
bfplToMathString : BigFPL -> String
bfplToMathString f =
    case f of
        Atom pname is ->
            pname ++ "_{" ++ (String.join "," <| List.map Aux_AE.toStringAExpr is) ++ "}"

        Neg p ->
            "\\neg " ++ bfplToMathString p

        Conj p q ->
            "( " ++ bfplToMathString p ++ " \\wedge " ++ bfplToMathString q ++ " )"

        Disj p q ->
            "( " ++ bfplToMathString p ++ " \\vee " ++ bfplToMathString q ++ " )"

        Impl p q ->
            "( " ++ bfplToMathString p ++ "\\rightarrow " ++ bfplToMathString q ++ " )"

        Equi p q ->
            "( " ++ bfplToMathString p ++ "\\leftrightarrow " ++ bfplToMathString q ++ " )"

        Insat ->
            "\\perp"

        Taut ->
            "\\top"

        BAnd li c p ->
            let
                c_string =
                    if c /= Aux_BE.T then
                        Aux_BE.toMathStringBExpr c

                    else
                        ""
            in
            "\\bigwedge \\limits_{ \\begin{array}{c} \\scriptsize " ++ (String.join "\\\\ \\scriptsize " <| List.map paramToMathString li) ++ "\\\\ \\scriptsize " ++ c_string ++ "\\end{array}} " ++ bfplToMathString p

        BOr li c p ->
            let
                c_string =
                    if c /= Aux_BE.T then
                        Aux_BE.toMathStringBExpr c

                    else
                        ""
            in
            "\\bigvee \\limits_{ \\begin{array}{c} \\scriptsize " ++ (String.join "\\\\ \\scriptsize " <| List.map paramToMathString li) ++ "\\\\ \\scriptsize " ++ c_string ++ "\\end{array}} " ++ bfplToMathString p


{-| It generates the String representation of a BigFPL formula in Latex Format, separating the representation of the formula and the representations of the conditions.
-}
bfplToMathString2 : BigFPL -> ( String, String )
bfplToMathString2 f =
    let
        ( fs, ls ) =
            bfplToMathStringAux f 1
    in
    ( fs
    , "\\begin{array}{l} \\scriptsize " ++ String.join "\\\\ \\scriptsize " ls ++ "\\end{array}"
    )


bfplToMathStringAux : BigFPL -> Int -> ( String, List String )
bfplToMathStringAux f i =
    case f of
        Insat ->
            ( "\\perp", [] )

        Taut ->
            ( "\\top", [] )

        Atom pname is ->
            ( pname ++ "_{" ++ (String.join "," <| List.map Aux_AE.toStringAExpr is) ++ "}"
            , []
            )

        Neg p ->
            let
                ( ps, ls ) =
                    bfplToMathStringAux p i
            in
            ( "\\neg " ++ ps, ls )

        Conj p q ->
            let
                ( ps, ls ) =
                    bfplToMathStringAux p i
            in
            let
                ( qs, ls2 ) =
                    bfplToMathStringAux q (i + List.length ls)
            in
            ( "( " ++ ps ++ " \\wedge " ++ qs ++ " )"
            , ls ++ ls2
            )

        Disj p q ->
            let
                ( ps, ls ) =
                    bfplToMathStringAux p i
            in
            let
                ( qs, ls2 ) =
                    bfplToMathStringAux q (i + List.length ls)
            in
            ( "( " ++ ps ++ " \\vee " ++ qs ++ " )"
            , ls ++ ls2
            )

        Impl p q ->
            let
                ( ps, ls ) =
                    bfplToMathStringAux p i
            in
            let
                ( qs, ls2 ) =
                    bfplToMathStringAux q (i + List.length ls)
            in
            ( "( " ++ ps ++ " \\rightarrow " ++ qs ++ " )"
            , ls ++ ls2
            )

        Equi p q ->
            let
                ( ps, ls ) =
                    bfplToMathStringAux p i
            in
            let
                ( qs, ls2 ) =
                    bfplToMathStringAux q (i + List.length ls)
            in
            ( "( " ++ ps ++ " \\leftrightarrow " ++ qs ++ " )"
            , ls ++ ls2
            )

        BAnd li c p ->
            if c /= Aux_BE.T then
                let
                    ( ps, ls ) =
                        bfplToMathStringAux p (i + 1)
                in
                let
                    ( c_s1, c_s2 ) =
                        ( "\\theta_{" ++ String.fromInt i ++ "}\\equiv " ++ Aux_BE.toMathStringBExpr c
                        , "s.t. \\, \\theta_{" ++ String.fromInt i ++ "}"
                        )
                in
                ( "\\bigwedge \\limits_{ \\begin{array}{c} \\scriptsize " ++ (String.join "\\\\ \\scriptsize " <| List.map paramToMathString li) ++ "\\\\ \\scriptsize " ++ c_s2 ++ "\\end{array}} " ++ ps
                , c_s1 :: ls
                )

            else
                let
                    ( ps, ls ) =
                        bfplToMathStringAux p i
                in
                ( "\\bigwedge \\limits_{ \\begin{array}{c} \\scriptsize " ++ (String.join "\\\\ \\scriptsize " <| List.map paramToMathString li) ++ "\\end{array}} " ++ ps
                , ls
                )

        BOr li c p ->
            if c /= Aux_BE.T then
                let
                    ( ps, ls ) =
                        bfplToMathStringAux p (i + 1)
                in
                let
                    ( c_s1, c_s2 ) =
                        ( "\\theta_{" ++ String.fromInt i ++ "}\\equiv " ++ Aux_BE.toMathStringBExpr c
                        , "s.t. \\, \\theta_{" ++ String.fromInt i ++ "}"
                        )
                in
                ( "\\bigvee \\limits_{ \\begin{array}{c} \\scriptsize " ++ (String.join "\\\\ \\scriptsize " <| List.map paramToMathString li) ++ "\\\\ \\scriptsize " ++ c_s2 ++ "\\end{array}} " ++ ps
                , c_s1 :: ls
                )

            else
                let
                    ( ps, ls ) =
                        bfplToMathStringAux p i
                in
                ( "\\bigvee \\limits_{ \\begin{array}{c} \\scriptsize " ++ (String.join "\\\\ \\scriptsize " <| List.map paramToMathString li) ++ "\\end{array}} " ++ ps
                , ls
                )


{-| It gives the true variables of the model in a string
-}
solutionModelToString : Interpretation -> String
solutionModelToString i =
    PL_SS.splToString <| List.map PL_SS.Atom i


{-| It gives the true variables of the model in a string in Latex format
-}
solutionModelToMathString : Interpretation -> String
solutionModelToMathString i =
    PL_SS.splToMathString2 <| List.map PL_SS.Atom i



