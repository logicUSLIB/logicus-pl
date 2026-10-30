module PLOracle exposing
    ( atoms, formula, formulaSet, clause, clauseSet
    , eval, evalSet, evalClause, evalClauseSet
    , symbols, symbolsSet, clauseSymbols, interpretations
    , satisfiable, satisfiableClauses, equivalent, entails, clausesEquivalentTo, cnfClauses, models, toSet
    , isNNF, isCNF, isDNF, isLiteral
    )

{-| Reference semantics for propositional logic, written independently of the
library, plus fuzzers for small formulas. Every semantic test compares a
library result against these functions.
-}

import Fuzz exposing (Fuzzer)
import List.Extra as LE
import LogicUS.PL.Clauses exposing (ClausePL, ClausePLSet)
import LogicUS.PL.SyntaxSemantics exposing (FormulaPL(..), PSymb, SetPL)
import Set exposing (Set)



-- FUZZERS


atoms : List PSymb
atoms =
    [ ( "p", [] ), ( "q", [] ), ( "r", [] ), ( "s", [] ) ]


leaf : Fuzzer FormulaPL
leaf =
    Fuzz.frequency
        [ ( 10, Fuzz.map Atom (Fuzz.oneOfValues atoms) )
        , ( 1, Fuzz.constant Insat )
        , ( 1, Fuzz.constant Taut )
        ]


{-| Random formula of at most the given depth over p, q, r, s.
-}
formula : Int -> Fuzzer FormulaPL
formula depth =
    if depth <= 0 then
        leaf

    else
        let
            sub =
                Fuzz.lazy (\_ -> formula (depth - 1))
        in
        Fuzz.frequency
            [ ( 2, leaf )
            , ( 2, Fuzz.map Neg sub )
            , ( 2, Fuzz.map2 Conj sub sub )
            , ( 2, Fuzz.map2 Disj sub sub )
            , ( 2, Fuzz.map2 Impl sub sub )
            , ( 1, Fuzz.map2 Equi sub sub )
            ]


formulaSet : Int -> Int -> Fuzzer SetPL
formulaSet maxSize depth =
    Fuzz.listOfLengthBetween 1 maxSize (formula depth)


clause : Fuzzer ClausePL
clause =
    Fuzz.listOfLengthBetween 0 3 (Fuzz.pair (Fuzz.oneOfValues atoms) Fuzz.bool)


clauseSet : Fuzzer ClausePLSet
clauseSet =
    Fuzz.listOfLengthBetween 1 7 (Fuzz.listOfLengthBetween 1 3 (Fuzz.pair (Fuzz.oneOfValues atoms) Fuzz.bool))



-- SEMANTICS


eval : Set PSymb -> FormulaPL -> Bool
eval i f =
    case f of
        Atom a ->
            Set.member a i

        Neg g ->
            not (eval i g)

        Conj a b ->
            eval i a && eval i b

        Disj a b ->
            eval i a || eval i b

        Impl a b ->
            not (eval i a) || eval i b

        Equi a b ->
            eval i a == eval i b

        Insat ->
            False

        Taut ->
            True


evalSet : Set PSymb -> SetPL -> Bool
evalSet i fs =
    List.all (eval i) fs


evalClause : Set PSymb -> ClausePL -> Bool
evalClause i c =
    List.any (\( a, pol ) -> Set.member a i == pol) c


evalClauseSet : Set PSymb -> ClausePLSet -> Bool
evalClauseSet i cs =
    List.all (evalClause i) cs


symbols : FormulaPL -> Set PSymb
symbols f =
    case f of
        Atom a ->
            Set.singleton a

        Neg g ->
            symbols g

        Conj a b ->
            Set.union (symbols a) (symbols b)

        Disj a b ->
            Set.union (symbols a) (symbols b)

        Impl a b ->
            Set.union (symbols a) (symbols b)

        Equi a b ->
            Set.union (symbols a) (symbols b)

        _ ->
            Set.empty


symbolsSet : SetPL -> Set PSymb
symbolsSet fs =
    List.foldl (\f acc -> Set.union (symbols f) acc) Set.empty fs


clauseSymbols : ClausePLSet -> Set PSymb
clauseSymbols cs =
    Set.fromList (List.concatMap (List.map Tuple.first) cs)


{-| All interpretations (sets of true symbols) over the given symbols.
-}
interpretations : Set PSymb -> List (Set PSymb)
interpretations syms =
    LE.subsequences (Set.toList syms) |> List.map Set.fromList


satisfiable : SetPL -> Bool
satisfiable fs =
    List.any (\i -> evalSet i fs) (interpretations (symbolsSet fs))


{-| Satisfiability of a clause set with a plain DPLL (unit propagation and
splitting), so that sets with many auxiliary symbols stay cheap.
-}
satisfiableClauses : ClausePLSet -> Bool
satisfiableClauses cs =
    dpllSat (List.map (List.map (\( a, pol ) -> ( a, pol ))) cs)


dpllSat : List (List ( PSymb, Bool )) -> Bool
dpllSat cs =
    if List.isEmpty cs then
        True

    else if List.any List.isEmpty cs then
        False

    else
        case List.head (List.filter (\c -> List.length c == 1) cs) of
            Just [ lit ] ->
                dpllSat (assign lit cs)

            _ ->
                case List.head cs |> Maybe.andThen List.head of
                    Just ( a, _ ) ->
                        dpllSat (assign ( a, True ) cs) || dpllSat (assign ( a, False ) cs)

                    Nothing ->
                        True


assign : ( PSymb, Bool ) -> List (List ( PSymb, Bool )) -> List (List ( PSymb, Bool ))
assign ( a, v ) cs =
    cs
        |> List.filter (\c -> not (List.member ( a, v ) c))
        |> List.map (List.filter (\( b, _ ) -> b /= a))


equivalent : FormulaPL -> FormulaPL -> Bool
equivalent f g =
    interpretations (Set.union (symbols f) (symbols g))
        |> List.all (\i -> eval i f == eval i g)


entails : SetPL -> FormulaPL -> Bool
entails fs g =
    interpretations (Set.union (symbolsSet fs) (symbols g))
        |> List.all (\i -> not (evalSet i fs) || eval i g)


{-| The clause set has exactly the same models as the formula set (both
interpreted over the union of their symbols).
-}
clausesEquivalentTo : SetPL -> ClausePLSet -> Bool
clausesEquivalentTo fs cs =
    -- A clause form that introduces new symbols (e.g. Tseitin) is not
    -- equivalent in the classical sense; rejecting it early also avoids
    -- enumerating 2^n interpretations.
    if not (Set.isEmpty (Set.diff (clauseSymbols cs) (symbolsSet fs))) then
        False

    else
        interpretations (symbolsSet fs)
            |> List.all (\i -> evalSet i fs == evalClauseSet i cs)


{-| Clauses of a formula already in CNF (Nothing if it is not in CNF).
-}
cnfClauses : FormulaPL -> Maybe ClausePLSet
cnfClauses f =
    let
        lits g =
            case g of
                Disj a b ->
                    Maybe.map2 (++) (lits a) (lits b)

                Atom a ->
                    Just [ Just ( a, True ) ]

                Neg (Atom a) ->
                    Just [ Just ( a, False ) ]

                Insat ->
                    Just []

                Taut ->
                    Just [ Nothing ]

                _ ->
                    Nothing

        clauses g =
            case g of
                Conj a b ->
                    Maybe.map2 (++) (clauses a) (clauses b)

                _ ->
                    lits g
                        |> Maybe.map
                            (\ls ->
                                if List.member Nothing ls then
                                    []

                                else
                                    [ List.filterMap identity ls ]
                            )
    in
    clauses f


{-| Models over the given symbols, as a set of sorted symbol lists.
-}
models : Set PSymb -> SetPL -> Set (List PSymb)
models syms fs =
    interpretations syms
        |> List.filter (\i -> evalSet i fs)
        |> List.map Set.toList
        |> Set.fromList


toSet : List (List PSymb) -> Set (List PSymb)
toSet is =
    is |> List.map (Set.fromList >> Set.toList) |> Set.fromList



-- SHAPES


isLiteral : FormulaPL -> Bool
isLiteral f =
    case f of
        Atom _ ->
            True

        Neg (Atom _) ->
            True

        Insat ->
            True

        Taut ->
            True

        _ ->
            False


isNNF : FormulaPL -> Bool
isNNF f =
    case f of
        Conj a b ->
            isNNF a && isNNF b

        Disj a b ->
            isNNF a && isNNF b

        _ ->
            isLiteral f


isClauseF : FormulaPL -> Bool
isClauseF f =
    case f of
        Disj a b ->
            isClauseF a && isClauseF b

        _ ->
            isLiteral f


isCNF : FormulaPL -> Bool
isCNF f =
    case f of
        Conj a b ->
            isCNF a && isCNF b

        _ ->
            isClauseF f


isCubeF : FormulaPL -> Bool
isCubeF f =
    case f of
        Conj a b ->
            isCubeF a && isCubeF b

        _ ->
            isLiteral f


isDNF : FormulaPL -> Bool
isDNF f =
    case f of
        Disj a b ->
            isDNF a && isDNF b

        _ ->
            isCubeF f
