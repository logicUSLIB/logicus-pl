module LogicUS.PL.Resolution exposing
    ( ResolutionTableau
    , cplResolventByPSymb, cplAllResolvents, csplAllResolventsByPsymb, csplResolventsByClause, csplAllResolvents
    , csplSaturationResolution, csplRegularResolution
    , csplSCFResolution, csplSCFLinearResolution, csplSCFPositiveResolution, csplSCFNegativeResolution
    , csplSCFUnitaryResolution, csplSCFByEntriesResolution
    , resolutionProcessListToMathString, resolutionProcessListToString, resolutionProcessListToStringTable, resolutionTableauToString, resolutionTableauToDOT, resolutionTableauToDOTStyled
    )

{-| The module provides the tools for aplying the differents resolution strategies to a set of propositional clauses for verifying its unfeasibility.


# Types

@docs ResolutionTableau


# Resolvents

@docs cplResolventByPSymb, cplAllResolvents, csplAllResolventsByPsymb, csplResolventsByClause, csplAllResolvents


# Saturation and Regular Resolution

@docs csplSaturationResolution, csplRegularResolution


# Refutationally Complete Resolution Algorithms

@docs csplSCFResolution, csplSCFLinearResolution, csplSCFPositiveResolution, csplSCFNegativeResolution


# Non Refutationally Complete Resolution Algorithms

@docs csplSCFUnitaryResolution, csplSCFByEntriesResolution


# Resolution Tableau Representation

@docs resolutionProcessListToMathString, resolutionProcessListToString, resolutionProcessListToStringTable, resolutionTableauToString, resolutionTableauToDOT, resolutionTableauToDOTStyled

-}

import Dict exposing (Dict)
import Graph exposing (Edge, Graph, Node)
import Graph.DOT exposing (defaultStyles)
import List.Extra as LE
import LogicUS.PL.AuxiliarFunctions exposing (uniqueConcatList)
import LogicUS.PL.Clauses as PL_CL exposing (ClausePL, ClausePLLiteral, ClausePLSet)
import LogicUS.PL.SyntaxSemantics as PL_SS exposing (FormulaPL(..), PSymb)
import Set


{-| Defines the Resolution Tableau type as a Graph whose node labels are pairs of a bool (indicates if the node is in the original clause set (True) or is a deduction (False)) and the clause considered in the corresponding node; and a edge label is just the literal of source node which is considered in the resolvent.
-}
type alias ResolutionTableau =
    Graph ( Bool, ClausePL ) ClausePLLiteral


type alias ResolutionItem =
    { c : ClausePL
    , p1 : Int
    , l1 : ClausePLLiteral
    , p2 : Int
    , l2 : ClausePLLiteral
    }



--===========--
-- FUNCTIONS --
--===========--
--------------------
-- Aux. Functions --
--------------------
-- It removes the resolution items whose clause is subsumed by other of other item.


filterSubsumedResolutionItems : List ResolutionItem -> List ResolutionItem
filterSubsumedResolutionItems xs =
    List.foldl
        (\x ac ->
            if List.any (\y -> PL_CL.cplSubsumes y.c x.c) ac then
                ac

            else
                ac ++ [ x ]
        )
        []
        (List.sortBy (\x -> List.length x.c) xs)



-----------------------
--  Module Functions --
-----------------------


{-| It gets the resolvent from two clauses by one literal. If it can be performed then it returns the resolvent and the literal considerated in each clause. If the resolvent does not exist it returns Nothing.

    cplResolventByPSymb [ ( "p", True ), ( "q", True ) ] [ ( "p", False ), ( "q", True ) ] "p" == Just ( [ ( "q", True ) ], ( "p", True ), ( "p", False ) )

    cplResolventByPSymb [ ( "p", True ), ( "q", True ) ] [ ( "p", False ), ( "q", True ) ] "q" == Nothing

-}
cplResolventByPSymb : ClausePL -> ClausePL -> PSymb -> Maybe ( ClausePL, ClausePLLiteral, ClausePLLiteral )
cplResolventByPSymb c1 c2 v =
    if List.member ( v, True ) c1 && List.member ( v, False ) c2 then
        Just <|
            ( PL_CL.cplSort <| uniqueConcatList [] <| List.filter (\x -> ( v, True ) /= x) c1 ++ List.filter (\x -> ( v, False ) /= x) c2
            , ( v, True )
            , ( v, False )
            )

    else if List.member ( v, True ) c2 && List.member ( v, False ) c1 then
        Just <|
            ( PL_CL.cplSort <| uniqueConcatList [] <| List.filter (\x -> ( v, False ) /= x) c1 ++ List.filter (\x -> ( v, True ) /= x) c2
            , ( v, False )
            , ( v, True )
            )

    else
        Nothing


{-| It gets all passible resolvents between two clauses. Note that if several resolvents can be performed then all of them are tautologies.

    cplAllResolvents [ ( "p", True ), ( "q", True ) ] [ ( "p", False ), ( "q", False ) ]
        == [ ( [ ( "q", False ), ( "q", True ) ], ( "p", True ), ( "p", False ) ), ( [ ( "p", False ), ( "p", True ) ], ( "q", True ), ( "q", False ) ) ]

    cplAllResolvents [ ( "p", True ), ( "q", True ) ] [ ( "p", False ), ( "q", True ) ]
        == [ ( [ ( "q", True ) ], ( "p", True ), ( "p", False ) ) ]

    cplAllResolvents [ ( "p", True ), ( "q", True ) ] [ ( "q", True ) ] == []

-}
cplAllResolvents : ClausePL -> ClausePL -> List ( ClausePL, ClausePLLiteral, ClausePLLiteral )
cplAllResolvents c1 c2 =
    Set.foldl
        (\v ac ->
            case cplResolventByPSymb c1 c2 v of
                Nothing ->
                    ac

                Just r ->
                    uniqueConcatList ac [ r ]
        )
        []
        (Set.intersect (Set.fromList <| PL_CL.cplSymbols c1) (Set.fromList <| PL_CL.cplSymbols c2))


{-| It gets the resolvents between the clauses of a set by the variable given.

    csplAllResolventsByPsymb [ [ ( "p", True ), ( "q", True ) ], [ ( "p", False ), ( "q", False ) ], [ ( "p", False ), ( "q", True ) ] ] "p"
        == [ [ ( "q", False ), ( "q", True ) ], [ ( "q", True ) ] ]

-}
csplAllResolventsByPsymb : List ClausePL -> PSymb -> List ClausePL
csplAllResolventsByPsymb cs v =
    Tuple.second <|
        List.foldl
            (\c2 ( cs_, res ) ->
                let
                    rs_c2 =
                        List.foldl
                            (\c1 ac ->
                                case cplResolventByPSymb c1 c2 v of
                                    Nothing ->
                                        ac

                                    Just ( cr, _, _ ) ->
                                        ac ++ [ cr ]
                            )
                            []
                            cs_
                in
                ( cs_ ++ [ c2 ], uniqueConcatList res rs_c2 )
            )
            ( [], [] )
            cs


{-| It gets all resolvents of each clause of a set with a clause given. It returns a list of a pair with the index of the formula with which the reference clause is resolved and all the resolvents obtained.

    csplResolventsByClause [ [ ( "p", True ), ( "q", True ) ], [ ( "p", False ), ( "q", False ) ] ] [ ( "p", False ), ( "q", True ) ]
        == [ ( 0, [ ( [ ( "q", True ) ], ( "p", False ), ( "p", True ) ) ] ), ( 1, [ ( [ ( "p", False ) ], ( "q", True ), ( "q", False ) ) ] ) ]

-}
csplResolventsByClause : List ClausePL -> ClausePL -> List ( Int, List ( ClausePL, ClausePLLiteral, ClausePLLiteral ) )
csplResolventsByClause cs c =
    List.indexedMap
        (\i ci ->
            ( i
            , cplAllResolvents c ci
            )
        )
        cs


{-| It gets all possible resolvents each two clauses of the set, and gives it as a clause set ommitting who are the parents and removing duplicated clauses.

    csplAllResolvents [ [ ( "p", True ), ( "q", True ) ], [ ( "p", False ), ( "q", False ) ], [ ( "p", False ), ( "q", True ) ] ]
        == [ [ ( "q", False ), ( "q", True ) ], [ ( "p", False ), ( "p", True ) ], [ ( "q", True ) ], [ ( "p", False ) ] ]

-}
csplAllResolvents : List ClausePL -> List ClausePL
csplAllResolvents cs =
    Tuple.second <|
        List.foldl
            (\c ( prev, ac ) ->
                let
                    ri =
                        List.map (\( x, _, _ ) -> x) <| List.concat <| List.map (\c2 -> cplAllResolvents c c2) prev
                in
                ( prev ++ [ c ], uniqueConcatList ac ri )
            )
            ( [], [] )
            cs



--===========================
--== SATURATION RESOLUTION ==
--===========================


{-| It uses saturation resolution algorithm for determining the feasibilibity of a set ot clauses. It gives the insatisfactibility (True:Insat, False:SAT) and the clause set considerated in each step of the algorithm.

    cs = [[("p",False),("q",False),("r",True)],[("q",True),("p",True)],[("r",False),("p",True)],[("p",False),("q",True)],[("q",False),("p",True)],[("p",False),("r",False)]]

    csplSaturationResolution  cs
        == (True,[[[("p",False),("q",False),("r",True)],[("q",True),("p",True)],[("r",False),("p",True)],[("p",False),("q",True)],[("q",False),("p",True)],[("p",False),("r",False)],[("q",False),("q",True),("r",True)],[("p",False),("p",True),("r",True)],[("q",False),("r",False),("r",True)],[("p",False),("p",True),("q",False)],[("p",False),("r",True)],[("q",True)],...

-}
csplSaturationResolution : List ClausePL -> ( Bool, List (List ClausePL) )
csplSaturationResolution cs =
    csplSaturationResolutionAux cs []



-- It perfomes saturation resolution algorithm


csplSaturationResolutionAux : List ClausePL -> List (List ClausePL) -> ( Bool, List (List ClausePL) )
csplSaturationResolutionAux cs hist =
    if List.any List.isEmpty cs then
        ( True, hist )

    else
        let
            known =
                List.map PL_CL.cplSort cs

            -- Only the resolvents not obtained before: the set is saturated (and satisfiable)
            -- when a level adds no new clause.
            cs2 =
                csplAllResolvents cs
                    |> List.map PL_CL.cplSort
                    |> LE.unique
                    |> List.filter (\c -> not (List.member c known))
        in
        if List.isEmpty cs2 then
            ( False, hist ++ [ cs ] )

        else
            csplSaturationResolutionAux (cs ++ cs2) (hist ++ [ cs ++ cs2 ])



--========================
--== REGULAR RESOLUTION ==
--========================


{-| It uses regular resolution algorithm for determining the feasibilibity of a set ot clauses. It gives the insatisfactibility (True:Insat, False:SAT) and the clause set considerated in each step of the algorithm.

    csplRegularResolution [ "p", "q", "r" ] cs
        == ( True, [ [ [ ( "p", False ), ( "q", False ), ( "r", True ) ], [ ( "q", True ), ( "p", True ) ], [ ( "r", False ), ( "p", True ) ], [ ( "p", False ), ( "q", True ) ], [ ( "q", False ), ( "p", True ) ], [ ( "p", False ), ( "r", False ) ] ], [ [ ( "q", False ), ( "q", True ), ( "r", True ) ], [ ( "q", False ), ( "r", False ), ( "r", True ) ], [ ( "q", True ) ], [ ( "q", True ), ( "r", False ) ], [ ( "q", False ), ( "r", True ) ], [ ( "q", False ), ( "q", True ) ], [ ( "r", False ) ], [ ( "q", False ), ( "r", False ) ] ], [ [ ( "r", False ) ], [ ( "r", False ), ( "r", True ) ], [ ( "r", True ) ], [ ( "r", False ) ] ], [ [] ] ] )

-}
csplRegularResolution : List PSymb -> List ClausePL -> ( Bool, List ClausePLSet )
csplRegularResolution vars clauses =
    let
        cs =
            (PL_CL.csplRemoveSubsumedClauses << PL_CL.csplRemoveTautClauses) clauses
    in
    let
        new_vars =
            uniqueConcatList [] (vars ++ PL_CL.csplSymbols cs)
    in
    Maybe.withDefault ( False, [] ) <| csplRegularResolutionAux [] new_vars cs


csplRegularResolutionAux : List ClausePLSet -> List PSymb -> ClausePLSet -> Maybe ( Bool, List ClausePLSet )
csplRegularResolutionAux hist vars clauses =
    case clauses of
        [] ->
            Just ( False, hist ++ [ clauses ] )

        [ [] ] ->
            Just ( True, hist ++ [ clauses ] )

        _ ->
            case vars of
                v :: vs ->
                    let
                        ( u1, u2 ) =
                            List.partition (List.all (\x -> Tuple.first x /= v)) clauses
                    in
                    csplRegularResolutionAux (hist ++ [ clauses ]) vs <| PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| u1 ++ csplAllResolventsByPsymb u2 v

                [] ->
                    Nothing



--===========================
--== RESOLUTION STRATEGIES ==
--===========================
-- It extracts the path (nodes and edges) to a resolution item in the following resolution algorithms.


recoverResolutionPath : Int -> Dict Int ResolutionItem -> ( List (Node ClausePL), List (Edge ClausePLLiteral) )
recoverResolutionPath i refDict =
    case Dict.get i refDict of
        Just ri ->
            let
                ( nodes1, edges1 ) =
                    recoverResolutionPath ri.p1 refDict

                ( nodes2, edges2 ) =
                    recoverResolutionPath ri.p2 refDict
            in
            ( uniqueConcatList nodes1 nodes2 ++ [ Node i ri.c ]
            , uniqueConcatList edges1 edges2 ++ [ Edge ri.p1 i ri.l1, Edge ri.p2 i ri.l2 ]
            )

        _ ->
            ( [], [] )



--=======================
--== COMMON RESOLUTION ==
--=======================
-- It gets the resolvents of one clause and the closed (explored) clauses


resolventsWithClosedSCFResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFResolutionAux closed id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) closed then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        closed



-- It updates the list of opened (unexplored) clauses given it as a pair whose first component corresponds to length (heuristic) of the clause and the second one to the clause properly.


openedUpdationSCFResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( lx, _ ) -> lx <= li) rest
                    in
                    if List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.filter (\( _, x ) -> not (PL_CL.cplSubsumes ri.c x.c)) <| List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res



-- It performs the resolution algoritm with only Shortest Clause First heuristic.


csplSCFResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge ClausePLLiteral) )
csplSCFResolutionAux closed opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( _, ri ) :: xs ->
            if List.isEmpty ri.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ [ ( nid + 1, ri ) ]
                in
                recoverResolutionPath (nid + 1) refDict

            else
                let
                    r_closed =
                        resolventsWithClosedSCFResolutionAux closed (nid + 1) ri.c
                in
                let
                    new_closed =
                        closed ++ [ ( nid + 1, ri ) ]

                    new_opened =
                        openedUpdationSCFResolutionAux xs (List.sortBy (\x -> Tuple.first x) <| List.map (\x -> ( List.length x.c, x )) r_closed)
                in
                csplSCFResolutionAux new_closed new_opened (nid + 1)


{-| It uses resolution algorithm using shortes clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFResolution = csplSCFResolution cs
    Tuple.first res_SCFResolution == True
    res_SCFResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 6 [label=\"q\"]\n  2 -> 8 [label=\"p\"]\n  3 -> 10 [label=\"q\"]\n  5 -> 6 [label=\"¬ q\"]\n  6 -> 11 [label=\"p\"]\n  7 -> 8 [label=\"¬ p\"]\n  8 -> 12 [label=\"¬ r\"]\n  9 -> 10 [label=\"¬ q\"]\n  10 -> 11 [label=\"¬ p\"]\n  11 -> 12 [label=\"r\"]\n\n  1 [label=\"{p,q}\"]\n  2 [label=\"{p,¬ r}\"]\n  3 [label=\"{¬ p,q}\"]\n  5 [label=\"{p,¬ q}\"]\n  6 [label=\"{p}\"]\n  7 [label=\"{¬ p,¬ r}\"]\n  8 [label=\"{¬ r}\"]\n  9 [label=\"{¬ p,¬ q,r}\"]\n  10 [label=\"{¬ p,r}\"]\n  11 [label=\"{r}\"]\n  12 [label=\"□\"]\n\n  {rank=same; 1;2;3;5;7;9;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOt_ as we show in the example above.

-}
csplSCFResolution : List ClausePL -> ( Bool, ResolutionTableau )
csplSCFResolution clauses =
    let
        cs =
            PL_CL.csplRemoveEqClauses clauses
    in
    let
        new_cs =
            List.sortBy (\x -> Tuple.first x) <| List.map (\x -> ( List.length x, { c = x, p1 = 0, p2 = 0, l1 = ( ( "", [] ), True ), l2 = ( ( "", [] ), False ) } )) <| PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFResolutionAux [] new_cs 0
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--=======================
--== LINEAR RESOLUTION ==
--=======================
-- It calculates the resolvents with closed clauses


resolventsWithClosedSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFLinearResolutionAux closed resDone id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) closed then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        (List.filter (\( i, _ ) -> not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone) <| closed)



-- It calculates the resolvents with opened clauses


resolventsWithOpenedSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFLinearResolutionAux opened id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) opened then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        opened



-- It performs the linear resolution algorithm with SCF heuristic


csplSCFLinearResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge ClausePLLiteral) )
csplSCFLinearResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        filterSubsumedResolutionItems <|
                            List.sortBy (\x -> List.length x.c) <|
                                resolventsWithClosedSCFLinearResolutionAux closed resDone id rid.c
                                    ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFLinearResolutionAux xs id rid.c)
                in
                let
                    newClosed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first <| closed ++ xs) <| Dict.map (\_ v -> v ++ [ id ]) resDone
                in
                Maybe.withDefault ( [], [] ) <|
                    List.head <|
                        List.filter
                            (not << List.isEmpty << Tuple.first)
                        <|
                            List.map
                                (\ri -> csplSCFLinearResolutionAux newClosed newResDone (( nid + 1, ri ) :: xs) (nid + 1))
                                resolvents_i


{-| It uses linear resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFLinearResolution = csplSCFLinearResolution cs
    Tuple.first res_SCFLinearResolution == True
    res_SCFLinearResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 8 [label=\"p\"]\n  3 -> 8 [label=\"¬ p\"]\n  4 -> 9 [label=\"¬ q\"]\n  5 -> 10 [label=\"¬ p\"]\n  6 -> 11 [label=\"r\"]\n  8 -> 9 [label=\"q\"]\n  8 -> 12 [label=\"q\"]\n  9 -> 10 [label=\"p\"]\n  9 -> 13 [label=\"p\"]\n  10 -> 11 [label=\"¬ r\"]\n  11 -> 12 [label=\"¬ q\"]\n  12 -> 13 [label=\"¬ p\"]\n\n  1 [label=\"{p,q}\"]\n  3 [label=\"{¬ p,q}\"]\n  4 [label=\"{p,¬ q}\"]\n  5 [label=\"{¬ p,¬ r}\"]\n  6 [label=\"{¬ p,¬ q,r}\"]\n  8 [label=\"{q}\"]\n  9 [label=\"{p}\"]\n  10 [label=\"{¬ r}\"]\n  11 [label=\"{¬ p,¬ q}\"]\n  12 [label=\"{¬ p}\"]\n  13 [label=\"□\"]\n  14 [label=\"{p,¬ r}\"]\n\n  {rank=same; 1;3;4;5;6;14;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFLinearResolution : List ClausePL -> ( Bool, ResolutionTableau )
csplSCFLinearResolution clauses =
    let
        cs =
            PL_CL.csplRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = ( ( "", [] ), True ), l2 = ( ( "", [] ), False ) } )) <| List.sortBy (\x -> List.length x) <| PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| cs
    in
    let
        -- Linear resolution is complete only if every input clause may be the top clause:
        -- try them in order (shortest first) until one gives a refutation.
        ( nodes, edges ) =
            List.range 0 (List.length new_cs - 1)
                |> LE.findMap
                    (\k ->
                        let
                            rotated =
                                List.drop k new_cs ++ List.take k new_cs

                            result =
                                csplSCFLinearResolutionAux [] Dict.empty rotated (List.length new_cs + 1)
                        in
                        if List.isEmpty (Tuple.first result) then
                            Nothing

                        else
                            Just result
                    )
                |> Maybe.withDefault ( [], [] )
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



-- --=========================
-- --== POSITIVE RESOLUTION ==
-- --=========================


openedUpdationSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFPositiveResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFPositiveResolutionAux closed resDone id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) closed then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        (List.filter (\( i, ri ) -> (PL_CL.cplIsPositive c || PL_CL.cplIsPositive ri.c) && (not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone)) <| closed)


resolventsWithOpenedSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFPositiveResolutionAux opened id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) opened then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        (List.filter (\( _, ri ) -> PL_CL.cplIsPositive c || PL_CL.cplIsPositive ri.c) <| opened)


csplSCFPositiveResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge ClausePLLiteral) )
csplSCFPositiveResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFPositiveResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFPositiveResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFPositiveResolutionAux xs resolvents_i
                in
                csplSCFPositiveResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses positive resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFPositiveResolution = csplSCFPositiveResolution cs
    Tuple.first res_SCFPositiveResolution == True
    res_SCFPositiveResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 8 [label=\"p\"]\n  1 -> 9 [label=\"q\"]\n  3 -> 8 [label=\"¬ p\"]\n  4 -> 9 [label=\"¬ q\"]\n  5 -> 14 [label=\"¬ p\"]\n  6 -> 12 [label=\"¬ q\"]\n  8 -> 12 [label=\"q\"]\n  9 -> 14 [label=\"p\"]\n  9 -> 15 [label=\"p\"]\n  12 -> 15 [label=\"¬ p\"]\n  14 -> 17 [label=\"¬ r\"]\n  15 -> 17 [label=\"r\"]\n\n  1 [label=\"{p,q}\"]\n  3 [label=\"{¬ p,q}\"]\n  4 [label=\"{p,¬ q}\"]\n  5 [label=\"{¬ p,¬ r}\"]\n  6 [label=\"{¬ p,¬ q,r}\"]\n  8 [label=\"{q}\"]\n  9 [label=\"{p}\"]\n  12 [label=\"{¬ p,r}\"]\n  14 [label=\"{¬ r}\"]\n  15 [label=\"{r}\"]\n  17 [label=\"□\"]\n  18 [label=\"{p,¬ r}\"]\n\n  {rank=same; 1;3;4;5;6;18;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFPositiveResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) ClausePLLiteral )
csplSCFPositiveResolution clauses =
    let
        cs =
            PL_CL.csplRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = ( ( "", [] ), True ), l2 = ( ( "", [] ), False ) } )) <| List.sortBy (\x -> List.length x) <| PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFPositiveResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--=========================
--== NEGATIVE RESOLUTION ==
--=========================


openedUpdationSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFNegativeResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFNegativeResolutionAux closed resDone id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) closed then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        (List.filter (\( i, ri ) -> (PL_CL.cplIsNegative c || PL_CL.cplIsNegative ri.c) && (not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone)) <| closed)


resolventsWithOpenedSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFNegativeResolutionAux opened id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) opened then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        (List.filter (\( _, ri ) -> PL_CL.cplIsNegative c || PL_CL.cplIsNegative ri.c) <| opened)


csplSCFNegativeResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge ClausePLLiteral) )
csplSCFNegativeResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFNegativeResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFNegativeResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFNegativeResolutionAux xs resolvents_i
                in
                csplSCFNegativeResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses negative resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFNegativeResolution = csplSCFNegativeResolution cs
    Tuple.first res_SCFNegativeResolution == True
    res_SCFNegativeResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n  1 -> 16 [label=\"p\"]\n  2 -> 10 [label=\"p\"]\n  3 -> 14 [label=\"q\"]\n  4 -> 17 [label=\"p\"]\n  5 -> 10 [label=\"¬ p\"]\n  6 -> 12 [label=\"r\"]\n  10 -> 12 [label=\"¬ r\"]\n  12 -> 14 [label=\"¬ q\"]\n  14 -> 16 [label=\"¬ p\"]\n  14 -> 17 [label=\"¬ p\"]\n  16 -> 19 [label=\"q\"]\n  17 -> 19 [label=\"¬ q\"]\n\n  1 [label=\"{p,q}\"]\n  2 [label=\"{p,¬ r}\"]\n  3 [label=\"{¬ p,q}\"]\n  4 [label=\"{p,¬ q}\"]\n  5 [label=\"{¬ p,¬ r}\"]\n  6 [label=\"{¬ p,¬ q,r}\"]\n  10 [label=\"{¬ r}\"]\n  12 [label=\"{¬ p,¬ q}\"]\n  14 [label=\"{¬ p}\"]\n  16 [label=\"{q}\"]\n  17 [label=\"{¬ q}\"]\n  19 [label=\"□\"]\n\n  {rank=same; 1;2;3;4;5;6;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFNegativeResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) ClausePLLiteral )
csplSCFNegativeResolution clauses =
    let
        cs =
            PL_CL.csplRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = ( ( "", [] ), True ), l2 = ( ( "", [] ), False ) } )) <| List.sortBy (\x -> List.length x) <| PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFNegativeResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



--========================
--== UNITARY RESOLUTION ==
--========================


openedUpdationSCFUnitaryResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFUnitaryResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFUnitaryResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ClausePL -> List ResolutionItem
resolventsWithClosedSCFUnitaryResolutionAux closed resDone id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) closed then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        (List.filter (\( i, ri ) -> (List.length c == 1 || List.length ri.c == 1) && (not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone)) <| closed)


resolventsWithOpenedSCFUnitaryResolutionAux : List ( Int, ResolutionItem ) -> Int -> ClausePL -> List ResolutionItem
resolventsWithOpenedSCFUnitaryResolutionAux opened id c =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) opened then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents c ri.c)
        )
        []
        (List.filter (\( _, ri ) -> List.length c == 1 || List.length ri.c == 1) <| opened)


csplSCFUnitaryResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge ClausePLLiteral) )
csplSCFUnitaryResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFUnitaryResolutionAux closed resDone id rid.c
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFUnitaryResolutionAux xs id rid.c)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFUnitaryResolutionAux xs resolvents_i
                in
                csplSCFUnitaryResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses unitary resolution algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFUnitaryResolution = csplSCFUnitaryResolution cs
    Tuple.first res_SCFUnitaryResolution == False
    res_SCFUnitaryResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n\n\n  1 [label=\"{¬ p,¬ q,r}\"]\n  2 [label=\"{p,q}\"]\n  3 [label=\"{p,¬ r}\"]\n  4 [label=\"{¬ p,q}\"]\n  5 [label=\"{p,¬ q}\"]\n  6 [label=\"{¬ p,¬ r}\"]\n\n  {rank=same; 1;2;3;4;5;6;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFUnitaryResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) ClausePLLiteral )
csplSCFUnitaryResolution clauses =
    let
        cs =
            PL_CL.csplRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = ( ( "", [] ), True ), l2 = ( ( "", [] ), True ) } )) <| List.sortBy (\x -> List.length x) <| PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFUnitaryResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



-- --===========================
-- --== BY ENTRIES RESOLUTION ==
-- --===========================


openedUpdationSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem ) -> List ( Int, ResolutionItem )
openedUpdationSCFByEntriesResolutionAux xs new_opens =
    let
        res =
            List.foldl
                (\( li, ri ) ( ac, rest ) ->
                    let
                        add_ac =
                            LE.takeWhile (\( _, x ) -> List.length x.c <= List.length ri.c) rest
                    in
                    if List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) (ac ++ add_ac) then
                        ( ac ++ add_ac, List.drop (List.length add_ac) rest )

                    else
                        ( ac ++ add_ac ++ [ ( li, ri ) ]
                        , List.drop (List.length add_ac) rest
                        )
                )
                ( [], xs )
                new_opens
    in
    Tuple.first res ++ Tuple.second res


resolventsWithClosedSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> Int -> ResolutionItem -> List ResolutionItem
resolventsWithClosedSCFByEntriesResolutionAux closed resDone id rid =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) closed then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents rid.c ri.c)
        )
        []
        (List.filter (\( i, ri ) -> (rid.p1 == 0 || ri.p1 == 0) && (not <| List.member id <| Maybe.withDefault [] <| Dict.get i resDone)) <| closed)


resolventsWithOpenedSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> Int -> ResolutionItem -> List ResolutionItem
resolventsWithOpenedSCFByEntriesResolutionAux opened id rid =
    List.foldl
        (\( i, ri ) ac ->
            List.foldl
                (\( cj, l1, l2 ) ac2 ->
                    if not <| PL_CL.cplIsTautology cj || List.any (\x -> PL_CL.cplSubsumes x.c cj) ac || List.any (\( _, x ) -> PL_CL.cplSubsumes x.c cj) opened then
                        { c = cj, p1 = id, l1 = l1, p2 = i, l2 = l2 } :: List.filter (\x -> not <| PL_CL.cplSubsumes cj x.c) ac2

                    else
                        ac2
                )
                ac
                (cplAllResolvents rid.c ri.c)
        )
        []
        (List.filter (\( _, ri ) -> rid.p1 == 0 || ri.p1 == 0) <| opened)


csplSCFByEntriesResolutionAux : List ( Int, ResolutionItem ) -> Dict Int (List Int) -> List ( Int, ResolutionItem ) -> Int -> ( List (Node ClausePL), List (Edge ClausePLLiteral) )
csplSCFByEntriesResolutionAux closed resDone opened nid =
    case opened of
        [] ->
            ( [], [] )

        ( id, rid ) :: xs ->
            if List.isEmpty rid.c then
                let
                    refDict =
                        Dict.fromList <| closed ++ opened
                in
                recoverResolutionPath id refDict

            else
                let
                    resolvents_i =
                        List.indexedMap (\i x -> ( nid + i + 1, x )) <|
                            filterSubsumedResolutionItems <|
                                List.sortBy (\x -> List.length x.c) <|
                                    resolventsWithClosedSCFByEntriesResolutionAux closed resDone id rid
                                        ++ (List.filter (\ri -> not <| List.any (\( _, x ) -> PL_CL.cplSubsumes x.c ri.c) closed) <| resolventsWithOpenedSCFByEntriesResolutionAux xs id rid)
                in
                let
                    new_closed =
                        closed ++ [ ( id, rid ) ]

                    newResDone =
                        Dict.insert id (List.map Tuple.first (closed ++ xs)) <| Dict.map (\_ v -> v ++ [ id ]) resDone

                    new_opened =
                        openedUpdationSCFByEntriesResolutionAux xs resolvents_i
                in
                csplSCFByEntriesResolutionAux new_closed newResDone new_opened (nid + List.length resolvents_i + 1)


{-| It uses resolution by entries algorithm using shortest clause first heuristic for determining the feasibilibity of a set of clauses. It gives the insatisfactibility (True:Insat, False:SAT) and a graph with the resolution path to inconsitence. If clause set is feasible then a graph with only initial nodes is returned.

    res_SCFByEntriesResolution = csplSCFByEntriesResolution cs
    Tuple.first res_SCFByEntriesResolution == False
    res_SCFByEntriesResolution |> Tuple.second |> resolutionTableauToDOT
        == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=box, color=black]\n  edge [dir=none, color=blue, fontcolor=blue]\n\n\n\n  1 [label=\"{¬ p,¬ q,r}\"]\n  2 [label=\"{p,q}\"]\n  3 [label=\"{p,¬ r}\"]\n  4 [label=\"{¬ p,q}\"]\n  5 [label=\"{p,¬ q}\"]\n  6 [label=\"{¬ p,¬ r}\"]\n\n  {rank=same; 1;2;3;4;5;6;}\n}"

Note: You can render the graph with GraphViz Viewer and _resolutionTableauToDOT_ described at the end.

-}
csplSCFByEntriesResolution : List ClausePL -> ( Bool, Graph ( Bool, ClausePL ) ClausePLLiteral )
csplSCFByEntriesResolution clauses =
    let
        cs =
            PL_CL.csplRemoveEqClauses clauses
    in
    let
        new_cs =
            List.indexedMap (\i x -> ( i + 1, { c = x, p1 = 0, p2 = 0, l1 = ( ( "", [] ), True ), l2 = ( ( "", [] ), False ) } )) <| List.sortBy (\x -> List.length x) <| PL_CL.csplRemoveSubsumedClauses <| PL_CL.csplRemoveTautClauses <| cs
    in
    let
        ( nodes, edges ) =
            csplSCFByEntriesResolutionAux [] Dict.empty new_cs (List.length new_cs + 1)
    in
    -- ( nodes, edges )
    let
        nid_max =
            Maybe.withDefault 0 <| List.maximum <| List.map (\x -> x.id) <| nodes

        nodes_clauses =
            List.map (\x -> x.label) <| nodes
    in
    let
        final_nodes =
            List.map (\x -> Node x.id ( List.member x.label cs, x.label )) nodes
                ++ (List.indexedMap (\i x -> Node (nid_max + i + 1) ( True, x )) <| List.filter (\x -> not (List.member x nodes_clauses)) cs)
    in
    ( edges /= [], Graph.fromNodesAndEdges final_nodes edges )



-- ----------------------------
--==============--
-- REPRESENTATON
--==============--


{-| It gives a string representation for a list of clauseSets from resolution process
-}
resolutionProcessListToString : List ClausePLSet -> String
resolutionProcessListToString hist =
    String.join "\n" <| List.map PL_CL.csplToString hist


{-| It gives a table as a string representation for a list of clauseSets from resolution process
-}
resolutionProcessListToStringTable : List ClausePLSet -> String
resolutionProcessListToStringTable hist =
    "step; set of clauses \n" ++ (String.join "\n" <| List.indexedMap (\i cs -> String.fromInt i ++ ";" ++ PL_CL.csplToString cs) hist)


{-| It gives a string representation in Latex notation for a list of clauseSets. It must be displayed in a math environment
-}
resolutionProcessListToMathString : List ClausePLSet -> String
resolutionProcessListToMathString hist =
    "\\begin{array}{c} " ++ (String.join "\\\\" <| List.map PL_CL.csplToMathString hist) ++ " \\end{array}"


{-| Express a Resolution Tableau as a string.
-}
resolutionTableauToString : ResolutionTableau -> String
resolutionTableauToString g =
    let
        toStringNode =
            \( _, cs ) -> Just <| PL_CL.cplToString cs

        toStringEdge =
            \l -> Just ((PL_SS.fplToString << PL_CL.clauseLitToLiteral) l)
    in
    Graph.toString toStringNode toStringEdge g


{-| Express a Resolution Tableau as a string in DOT format that is viewable with a GraphViz Render.
**Note:** If you are using elm repl, before introducing the code you must replace _\\n_ by _\\n_ and _\\"_ by _"_ in a simple text editor.
-}
resolutionTableauToDOT : ResolutionTableau -> String
resolutionTableauToDOT g =
    let
        toStringNode =
            \( _, cs ) -> Just <| PL_CL.cplToString cs

        toStringEdge =
            \l -> Just ((PL_SS.fplToString << PL_CL.clauseLitToLiteral) l)

        initialNodes =
            String.join ";" <|
                List.map String.fromInt <|
                    List.foldl
                        (\x ac ->
                            if Tuple.first x.label then
                                ac ++ [ x.id ]

                            else
                                ac
                        )
                        []
                        (Graph.nodes g)
    in
    String.replace "\n" "" <| String.replace "\n}" ("\n\n  {rank=same; " ++ initialNodes ++ ";}\n}") <| Graph.DOT.output toStringNode toStringEdge g


{-| Express a Resolution Tableau as a string in DOT format that is viewable with a GraphViz Render including some styles.
**Note:** If you are using elm repl, before introducing the code you must replace _\\n_ by _\\n_ and _\\"_ by _"_ in a simple text editor.
-}
resolutionTableauToDOTStyled : ResolutionTableau -> String
resolutionTableauToDOTStyled g =
    let
        myStyles =
            { defaultStyles | node = "shape=Mrecord, fillcolor=\"#c1f6ff\", style=filled, fontcolor=\"#1a2935\", color=\"#1a2935\"", edge = "color=\"#1a2935\", fontcolor=\"#1a2935\"" }

        toStringNode =
            \( _, cs ) -> Just <| PL_CL.cplToString cs

        toStringEdge =
            \l -> Just ((PL_SS.fplToString << PL_CL.clauseLitToLiteral) l)

        initialNodes =
            String.join ";" <|
                List.map String.fromInt <|
                    List.foldl
                        (\x ac ->
                            if Tuple.first x.label then
                                ac ++ [ x.id ]

                            else
                                ac
                        )
                        []
                        (Graph.nodes g)
    in
    String.replace "\n" "" <| String.replace "\"" ">" <| String.replace "=\"" "=<" <| String.replace "\n}" ("\n\n  {rank=same; " ++ initialNodes ++ ";}\n}") <| Graph.DOT.outputWithStyles myStyles toStringNode toStringEdge g
