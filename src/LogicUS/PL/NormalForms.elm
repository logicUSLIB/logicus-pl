module LogicUS.PL.NormalForms exposing (fplContainsEquiv, fplContainsDisj, fplContainsConj, fplRemoveAllEquiv, fplContainsImpl, fplRemoveAllImpl, fplInteriorizeAllDisj, fplInteriorizeAllConj, fplToNNF, fplToCNF, fplToDNF, dnfAsLiteralSets, cnfAsLiteralSets, fplSatisfiabilityDNF, fplModelsDNF, fplValidityCNF, fplToCNFTseitin, splToCNFTseitin, flpToCNFTseitin)

{-| The module provides the tools for express formulas in their NN, CNF, DNF.


# Normal Forms

@docs fplContainsEquiv, fplContainsDisj, fplContainsConj, fplRemoveAllEquiv, fplContainsImpl, fplRemoveAllImpl, fplInteriorizeAllDisj, fplInteriorizeAllConj, fplToNNF, fplToCNF, fplToDNF, dnfAsLiteralSets, cnfAsLiteralSets, fplSatisfiabilityDNF, fplModelsDNF, fplValidityCNF


# Tseitin transformation

@docs fplToCNFTseitin, splToCNFTseitin, flpToCNFTseitin

-}

--===========--
--  IMPORTS  --
--===========--

import LogicUS.PL.AuxiliarFunctions exposing (uniqueConcatList)
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..), Interpretation, SetPL)
import List exposing (length)
import List.Extra exposing (elemIndex, unique)
import LogicUS.PL.SyntaxSemantics exposing (PSymb)



--===========--
-- FUNCTIONS --
--===========--


{-|

    It checks if the formula contains any equivalence as a part of it.

    f1 = Neg (Equi (Atom "p") (Impl (Atom "q") (Atom "r")))
    fplContainsEquiv f1 == True

    f2 = Disj (Neg (Conj (Atom "p") (Conj (Atom "q") (Atom "r")))) (Disj (Conj (Atom "p") (Atom "q")) (Atom "r"))
    fplContainsEquiv f2 == False

-}
fplContainsEquiv : FormulaPL -> Bool
fplContainsEquiv f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsEquiv x

        Conj x y ->
            fplContainsEquiv x || fplContainsEquiv y

        Disj x y ->
            fplContainsEquiv x || fplContainsEquiv y

        Impl x y ->
            fplContainsEquiv x || fplContainsEquiv y

        Equi _ _ ->
            True

        Insat ->
            False

        Taut ->
            False


{-|

    It checks if the formula contains any implication as a part of the formula

    fplContainsImpl f1 == True

    fplContainsImpl f2 == False

-}
fplContainsImpl : FormulaPL -> Bool
fplContainsImpl f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsImpl x

        Conj x y ->
            fplContainsImpl x || fplContainsImpl y

        Disj x y ->
            fplContainsImpl x || fplContainsImpl y

        Impl _ _ ->
            True

        Equi x y ->
            fplContainsImpl x || fplContainsImpl y

        Insat ->
            False

        Taut ->
            False


{-| It checks if the formula contains any conjunction as a part of the formula

    fplContainsConj f1 == False

    fplContainsConj f2 == True

-}
fplContainsConj : FormulaPL -> Bool
fplContainsConj f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsConj x

        Conj _ _ ->
            True

        Disj x y ->
            fplContainsConj x || fplContainsConj y

        Impl x y ->
            fplContainsConj x || fplContainsConj y

        Equi x y ->
            fplContainsConj x || fplContainsConj y

        Insat ->
            False

        Taut ->
            False


{-|

    It checks if the formula contains any disjunction as a part of the formula

    fplContainsDisj f1 == False

    fplContainsDisj f2 == True

-}
fplContainsDisj : FormulaPL -> Bool
fplContainsDisj f =
    case f of
        Atom _ ->
            False

        Neg x ->
            fplContainsDisj x

        Conj x y ->
            fplContainsDisj x || fplContainsDisj y

        Disj _ _ ->
            True

        Impl x y ->
            fplContainsDisj x || fplContainsDisj y

        Equi x y ->
            fplContainsDisj x || fplContainsDisj y

        Insat ->
            False

        Taut ->
            False


{-|

    It eliminates all equivalences of a formula by replacing it with the conjunction of the corresponding implications.

    f3 = fplRemoveAllEquiv f1
    f3 == Neg (Conj (Impl (Atom "p") (Impl (Atom "q") (Atom "r"))) (Impl (Impl (Atom "q") (Atom "r")) (Atom "p")))

-}
fplRemoveAllEquiv : FormulaPL -> FormulaPL
fplRemoveAllEquiv f =
    case f of
        Atom x ->
            Atom x

        Neg x ->
            Neg (fplRemoveAllEquiv x)

        Conj x y ->
            Conj (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)

        Disj x y ->
            Disj (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)

        Impl x y ->
            Impl (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)

        Equi x y ->
            Conj (Impl (fplRemoveAllEquiv x) (fplRemoveAllEquiv y)) (Impl (fplRemoveAllEquiv y) (fplRemoveAllEquiv x))

        Insat ->
            Insat

        Taut ->
            Taut


{-|

    It eliminates all implications of a formula by replacing it with the conjunction of the corresponding implications.

    f4 = fplRemoveAllImpl f3
    f4 == Neg (Conj (Disj (Neg (Atom "p")) (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Neg (Disj (Neg (Atom "q")) (Atom "r"))) (Atom "p")))

-}
fplRemoveAllImpl : FormulaPL -> FormulaPL
fplRemoveAllImpl f =
    case f of
        Atom x ->
            Atom x

        Neg x ->
            Neg (fplRemoveAllImpl x)

        Conj x y ->
            Conj (fplRemoveAllImpl x) (fplRemoveAllImpl y)

        Disj x y ->
            Disj (fplRemoveAllImpl x) (fplRemoveAllImpl y)

        Impl x y ->
            Disj (Neg (fplRemoveAllImpl x)) (fplRemoveAllImpl y)

        Equi x y ->
            Conj (fplRemoveAllImpl <| Impl x y) (fplRemoveAllImpl <| Impl y x)

        Insat ->
            Insat

        Taut ->
            Taut


{-|

    It interiorizes the negations by applying De Morgan's laws where appropriate

    f5 = fpltoNNF f2
    f5 == Disj (Disj (Neg (Atom "p")) (Disj (Neg (Atom "q")) (Neg (Atom "r")))) (Disj (Conj (Atom "p") (Atom "q")) (Atom "r"))

    f6 = fplToNNF f4
    f6 == Disj (Conj (Atom "p") (Conj (Atom "q") (Neg (Atom "r")))) (Conj (Disj (Neg (Atom "q")) (Atom "r")) (Neg (Atom "p")))

-}
fplToNNF : FormulaPL -> FormulaPL
fplToNNF f =
    let
        fplToNNFAux p =
            case p of
                Atom x ->
                    Neg (Atom x)

                Neg x ->
                    fplToNNF x

                Conj x y ->
                    Disj (fplToNNFAux x) (fplToNNFAux y)

                Disj x y ->
                    Conj (fplToNNFAux x) (fplToNNFAux y)

                Impl x y ->
                    Conj (fplToNNF x) (fplToNNFAux y)

                Equi x y ->
                    Disj (Conj (fplToNNF x) (fplToNNFAux y)) (Conj (fplToNNFAux x) (fplToNNF y))

                Insat ->
                    Taut

                Taut ->
                    Insat
    in
    case f of
        Atom x ->
            Atom x

        Neg x ->
            fplToNNFAux x

        Conj x y ->
            Conj (fplToNNF x) (fplToNNF y)

        Disj x y ->
            Disj (fplToNNF x) (fplToNNF y)

        Impl x y ->
            Disj (fplToNNFAux x) (fplToNNF y)

        Equi x y ->
            Conj (Disj (fplToNNFAux x) (fplToNNF y)) (Disj (fplToNNFAux y) (fplToNNF x))

        Insat ->
            Insat

        Taut ->
            Taut


{-|

    It interiorizes the disjunctions by applying the AND Distributive law where appropriate.

    f7 = fplInteriorizeAllDisj f6
    f7 == Conj (Conj (Disj (Atom "p") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "p") (Neg (Atom "p")))) (Conj (Conj (Disj (Atom "q") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "q") (Neg (Atom "p")))) (Conj (Disj (Neg (Atom "r")) (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Neg (Atom "r")) (Neg (Atom "p")))))

-}
fplInteriorizeAllDisj : FormulaPL -> Maybe FormulaPL
fplInteriorizeAllDisj f =
    case f of
        Atom _ ->
            Just f

        Disj (Conj f1 f2) g ->
            fplInteriorizeAllDisj <| Conj (Disj f1 g) (Disj f2 g)

        Disj g (Conj f1 f2) ->
            fplInteriorizeAllDisj <| Conj (Disj g f1) (Disj g f2)

        Conj f1 f2 ->
            Maybe.map2 Conj (fplInteriorizeAllDisj f1) (fplInteriorizeAllDisj f2)

        Disj f1 f2 ->
            let
                g1 =
                    fplInteriorizeAllDisj f1

                g2 =
                    fplInteriorizeAllDisj f2
            in
            case g1 of
                Just (Conj x1 y1) ->
                    case g2 of
                        Just (Conj x2 y2) ->
                            fplInteriorizeAllDisj <| Disj (Conj x1 y1) (Conj x2 y2)

                        Just x2 ->
                            fplInteriorizeAllDisj <| Disj (Conj x1 y1) x2

                        _ ->
                            Nothing

                Just x1 ->
                    case g2 of
                        Just (Conj x2 y2) ->
                            fplInteriorizeAllDisj <| Disj x1 (Conj x2 y2)

                        Just x2 ->
                            Just <| Disj x1 x2

                        _ ->
                            Nothing

                _ ->
                    Nothing

        Neg (Atom _) ->
            Just f

        Insat ->
            Just Insat

        Taut ->
            Just Taut

        _ ->
            Nothing


{-|

    It interiorizes the conjunctions by applying the OR Distributive law where appropriate.

    f8 = fplInteriorizeAllConj f6
    f8 == Disj (Conj (Atom "p") (Conj (Atom "q") (Neg (Atom "r")))) (Disj (Conj (Neg (Atom "q")) (Neg (Atom "p"))) (Conj (Atom "r") (Neg (Atom "p"))))

-}
fplInteriorizeAllConj : FormulaPL -> Maybe FormulaPL
fplInteriorizeAllConj f =
    case f of
        Atom _ ->
            Just f

        Conj (Disj f1 f2) g ->
            fplInteriorizeAllConj <| Disj (Conj f1 g) (Conj f2 g)

        Conj g (Disj f1 f2) ->
            fplInteriorizeAllConj <| Disj (Conj g f1) (Conj g f2)

        Disj f1 f2 ->
            Maybe.map2 Disj (fplInteriorizeAllConj f1) (fplInteriorizeAllConj f2)

        Conj f1 f2 ->
            let
                g1 =
                    fplInteriorizeAllConj f1

                g2 =
                    fplInteriorizeAllConj f2
            in
            case g1 of
                Just (Disj x1 y1) ->
                    case g2 of
                        Just (Disj x2 y2) ->
                            fplInteriorizeAllConj <| Conj (Disj x1 y1) (Disj x2 y2)

                        Just x2 ->
                            fplInteriorizeAllConj <| Conj (Disj x1 y1) x2

                        _ ->
                            Nothing

                Just x1 ->
                    case g2 of
                        Just (Disj x2 y2) ->
                            fplInteriorizeAllConj <| Conj x1 (Disj x2 y2)

                        Just x2 ->
                            Just <| Conj x1 x2

                        _ ->
                            Nothing

                _ ->
                    Nothing

        Neg (Atom _) ->
            Just f

        Insat ->
            Just Insat

        Taut ->
            Just Taut

        _ ->
            Nothing


{-|

    Express a formula in its Conjuction Normal Form (CNF) that is formed as a conjuction of disjuntive formulas.

     -- Check if f1 is in CNF
    (f1 == fplToCNF f1) == False

    -- Check if f7 is in CNF
    (f7 == fplToCNF f7) == True

    -- Calculate CNF for f1
    f10 = fplToCNF f1
    f10 == Conj (Conj (Disj (Atom "p") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "p") (Neg (Atom "p")))) (Conj (Conj (Disj (Atom "q") (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Atom "q") (Neg (Atom "p")))) (Conj (Disj (Neg (Atom "r")) (Disj (Neg (Atom "q")) (Atom "r"))) (Disj (Neg (Atom "r")) (Neg (Atom "p")))))

    -- It is equal to f7
    (f10 == f7) == True

-}
fplToCNF : FormulaPL -> FormulaPL
fplToCNF f =
    Maybe.withDefault Insat <| fplInteriorizeAllDisj <| fplToNNF f


{-|

    Express a formula in its Disjunction Normal Form (CNF) that is formed as a conjuction of disjuntive formulas.

    -- Check if f1 is in DNF
    (f1 == fplToDNF f1) == False

    -- Check if f8 is in DNF
    (f8 == fplToCNF f8) == True

    -- Calculate CNF for f1
    f11 = fplToDNF f1
    f11 == Disj (Conj (Atom "p") (Conj (Atom "q") (Neg (Atom "r")))) (Disj (Conj (Neg (Atom "q")) (Neg (Atom "p"))) (Conj (Atom "r") (Neg (Atom "p"))))

    -- It is equal to f8
    (f11 == f8) == True

-}
fplToDNF : FormulaPL -> FormulaPL
fplToDNF f =
    Maybe.withDefault Insat <| fplInteriorizeAllConj <| fplToNNF f


{-| It gives a formula in DNF as a list of literal sets. If the formula given is not in DNF it returns Nothing.
-}
dnfAsLiteralSets : FormulaPL -> Maybe (List SetPL)
dnfAsLiteralSets f =
    literalSets False f


{-| It gives a formula in CNF as a list of literal sets. If the formula given is not in CNF it returns Nothing.
-}
cnfAsLiteralSets : FormulaPL -> Maybe (List SetPL)
cnfAsLiteralSets f =
    literalSets True f


{-| Shared implementation of `cnfAsLiteralSets` (`cnf = True`) and `dnfAsLiteralSets` (`cnf = False`).

In CNF the outer connective is ∧ and the groups are clauses (∨): a clause containing ⊤ is dropped, ⊥ inside a clause is
neutral and ⊥ alone is the empty clause. DNF is the dual (⊥ drops a conjunction, ⊤ is neutral in it).

-}
literalSets : Bool -> FormulaPL -> Maybe (List SetPL)
literalSets cnf f =
    let
        ( absorbing, neutral ) =
            if cnf then
                ( Taut, Insat )

            else
                ( Insat, Taut )

        normConst g =
            case g of
                Neg Insat ->
                    Taut

                Neg Taut ->
                    Insat

                _ ->
                    g

        -- Nothing: not in the expected form; Just Nothing: the group is absorbed (dropped)
        group : FormulaPL -> Maybe (Maybe SetPL)
        group g =
            case ( cnf, normConst g ) of
                ( True, Disj a b ) ->
                    Maybe.map2 (Maybe.map2 uniqueConcatList) (group a) (group b)

                ( False, Conj a b ) ->
                    Maybe.map2 (Maybe.map2 uniqueConcatList) (group a) (group b)

                ( _, Atom x ) ->
                    Just (Just [ Atom x ])

                ( _, Neg (Atom x) ) ->
                    Just (Just [ Neg (Atom x) ])

                ( _, h ) ->
                    if h == neutral then
                        Just (Just [])

                    else if h == absorbing then
                        Just Nothing

                    else
                        Nothing

        top : FormulaPL -> Maybe (List SetPL)
        top g =
            case ( cnf, normConst g ) of
                ( True, Conj a b ) ->
                    Maybe.map2 uniqueConcatList (top a) (top b)

                ( False, Disj a b ) ->
                    Maybe.map2 uniqueConcatList (top a) (top b)

                _ ->
                    group g
                        |> Maybe.map
                            (\m ->
                                case m of
                                    Just ls ->
                                        [ List.sortWith compareLiterals ls ]

                                    Nothing ->
                                        []
                            )
    in
    top f


{-| It gives if a set of literals has two that are contrary
-}
hasContraryLiterals : List FormulaPL -> Bool
hasContraryLiterals ls =
    case ls of
        [] ->
            False

        x :: xs ->
            List.member (PL_SS.fplNegation x) xs || hasContraryLiterals xs


{-| It solves the satisfiability of a formula by its DNF
-}
fplSatisfiabilityDNF : FormulaPL -> Bool
fplSatisfiabilityDNF f =
    let
        fls =
            Maybe.withDefault [] <| dnfAsLiteralSets <| fplToDNF f
    in
    List.any (not << hasContraryLiterals) fls


{-| It gets the models by DNF of a formula
-}
fplModelsDNF : FormulaPL -> List Interpretation
fplModelsDNF f =
    let
        fls =
            Maybe.withDefault [] <| dnfAsLiteralSets <| fplToDNF f
    in
    uniqueConcatList [] <| List.concat <| List.map (PL_SS.interpretationsFromSymbolsAndLiterals (PL_SS.fplSymbols f)) <| List.filter (not << hasContraryLiterals) fls


{-| It solves the validity of a formula by its CNF.
-}
fplValidityCNF : FormulaPL -> Bool
fplValidityCNF f =
    let
        fls =
            Maybe.withDefault [] <| cnfAsLiteralSets <| fplToCNF f
    in
    List.all hasContraryLiterals fls



-- It gives the order for the literals sets.


compareLiterals : FormulaPL -> FormulaPL -> Order
compareLiterals l1 l2 =
    case l1 of
        Atom x ->
            case l2 of
                Atom y ->
                    if x < y then
                        LT

                    else if x > y then
                        GT

                    else
                        EQ

                Neg (Atom y) ->
                    if x <= y then
                        LT

                    else
                        GT

                _ ->
                    LT

        Neg (Atom x) ->
            case l2 of
                Atom y ->
                    if x < y then
                        LT

                    else
                        GT

                Neg (Atom y) ->
                    if x < y then
                        LT

                    else if x > y then
                        GT

                    else
                        EQ

                _ ->
                    LT

        _ ->
            case l2 of
                Atom _ ->
                    GT

                Neg (Atom _) ->
                    GT

                _ ->
                    EQ



--=======================--
-- TSEITIN TRANSFORMATION --
--=======================--


{-| Fresh symbol used by the Tseitin transformation for the i-th compound subformula.
-}
tseitinSymbol : Int -> PSymb
tseitinSymbol i =
    ( "𝜏", [ i ] )


litNeg : FormulaPL -> FormulaPL
litNeg l =
    case l of
        Neg (Atom a) ->
            Atom a

        Insat ->
            Taut

        Taut ->
            Insat

        _ ->
            Neg l


{-| Builds a clause (as a disjunction) from literals: a clause with ⊤ is dropped and ⊥ literals are removed.
-}
tseitinClause : List FormulaPL -> List FormulaPL
tseitinClause lits =
    if List.member Taut lits then
        []

    else
        [ PL_SS.splDisjunction (unique (List.filter ((/=) Insat) lits)) ]


type alias TseitinState =
    { named : List FormulaPL
    , clauses : List FormulaPL
    }


{-| Gives the literal that stands for a subformula, adding the definitional clauses of the fresh symbol when needed.
-}
tseitinLiteral : FormulaPL -> TseitinState -> ( FormulaPL, TseitinState )
tseitinLiteral g st =
    case g of
        Atom _ ->
            ( g, st )

        Neg (Atom _) ->
            ( g, st )

        Insat ->
            ( g, st )

        Taut ->
            ( g, st )

        _ ->
            case elemIndex g st.named of
                Just i ->
                    ( Atom (tseitinSymbol i), st )

                Nothing ->
                    let
                        x =
                            Atom (tseitinSymbol (length st.named))

                        nx =
                            Neg x

                        st1 =
                            { st | named = st.named ++ [ g ] }

                        binary a b defs =
                            let
                                ( la, st2 ) =
                                    tseitinLiteral a st1

                                ( lb, st3 ) =
                                    tseitinLiteral b st2
                            in
                            ( x, { st3 | clauses = st3.clauses ++ List.concatMap tseitinClause (defs la lb) } )
                    in
                    case g of
                        Neg a ->
                            let
                                ( la, st2 ) =
                                    tseitinLiteral a st1
                            in
                            ( x, { st2 | clauses = st2.clauses ++ List.concatMap tseitinClause [ [ nx, litNeg la ], [ x, la ] ] } )

                        Conj a b ->
                            binary a b (\la lb -> [ [ nx, la ], [ nx, lb ], [ x, litNeg la, litNeg lb ] ])

                        Disj a b ->
                            binary a b (\la lb -> [ [ nx, la, lb ], [ x, litNeg la ], [ x, litNeg lb ] ])

                        Impl a b ->
                            binary a b (\la lb -> [ [ nx, litNeg la, lb ], [ x, la ], [ x, litNeg lb ] ])

                        Equi a b ->
                            binary a b (\la lb -> [ [ nx, litNeg la, lb ], [ nx, la, litNeg lb ], [ x, la, lb ], [ x, litNeg la, litNeg lb ] ])

                        _ ->
                            ( g, st )


{-| It performs the Tseitin transformation of a set of formulas. The result is a formula in CNF (at most three literals per clause) that is _equisatisfiable_ with the set, not equivalent to it: each compound subformula gets a fresh symbol `𝜏ᵢ` defined by an equivalence. Equal subformulas share their symbol, also across different formulas of the set, so the result grows linearly with the size of the set (the usual CNF may grow exponentially).

    splToCNFTseitin [ fplRead "p & q -> r" ]
        == Conj (Conj (Conj (Conj (Disj (Neg (Atom ( "𝜏", [ 0 ] ))) (Disj (Neg (Atom ( "𝜏", [ 1 ] ))) (Atom ( "r", [] )))) ...

-}
splToCNFTseitin : SetPL -> FormulaPL
splToCNFTseitin fs =
    let
        st =
            List.foldl
                (\f acc ->
                    let
                        ( l, acc2 ) =
                            tseitinLiteral f acc
                    in
                    { acc2 | clauses = acc2.clauses ++ tseitinClause [ l ] }
                )
                { named = [], clauses = [] }
                fs
    in
    if List.member Insat st.clauses then
        Insat

    else
        PL_SS.splConjunction (unique st.clauses)


{-| It performs the Tseitin transformation of a formula (see `splToCNFTseitin`).
-}
fplToCNFTseitin : FormulaPL -> FormulaPL
fplToCNFTseitin f =
    splToCNFTseitin [ f ]


{-| Deprecated: misspelled name kept for compatibility. Use `fplToCNFTseitin`.
-}
flpToCNFTseitin : FormulaPL -> FormulaPL
flpToCNFTseitin =
    fplToCNFTseitin
