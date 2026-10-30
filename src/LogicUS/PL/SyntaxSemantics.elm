module LogicUS.PL.SyntaxSemantics exposing
    ( PSymb, FormulaPL(..), Literal, SetPL, Interpretation
    , fplIsLiteral, fplIsPositiveLiteral, fplIsNegativeLiteral, fplNegation, fplSymbols, fplFormTree, fplValuation, fplInterpretations, fplModels, fplCountermodels, fplModelsCountermodels, fplTruthTable, fplSatisfiability, fplValidity, fplUnsatisfiability
    , splSymbols, splValuation, splInterpretations, splModels, splCountermodels, splModelsCountermodels, splTruthTable, splSatisfiability, splUnsatisfiability, logicalConsecuence, logicalConsecuence2
    , fplReadFromString, fplReadExtraction, fplRead, splRead, fplToInputString
    , interpretationReadFromString, interpretationReadExtraction
    , fplToString, fplToMathString, fplTruthTableString, fplTruthTableMathString, fplFormTreeToString, fplFormTreeToDOT
    , splToString, splToMathString, splToMathString2, splTruthTableString, splTruthTableMathString, splCompactTruthTableString, splCompactTruthTableMathString
    , interpretationToString, interpretationsToString, interpretationToMathString, interpretationsToMathString
    , interpretationsFromSymbolsAndLiterals, splConjunction, splDisjunction, splNegation
    )

{-| The module provides the elementary tools for working with propositional logic. It allows defining both formulas and sets as well as performing some basic operations on them, such as evaluations regarding interpretations, construction of truth tables, extraction of models and decision of satisfaction, tautology and logical consequence.


# Definition Types

@docs PSymb, FormulaPL, Literal, SetPL, Interpretation


# Work with PL Formulas

@docs fplIsLiteral, fplIsPositiveLiteral, fplIsNegativeLiteral, fplNegation, fplSymbols, fplFormTree, fplValuation, fplInterpretations, fplModels, fplCountermodels, fplModelsCountermodels, fplTruthTable, fplSatisfiability, fplValidity, fplUnsatisfiability


# Work with PL Sets

@docs splSymbols, splValuation, splInterpretations, splModels, splCountermodels, splModelsCountermodels, splTruthTable, splSatisfiability, splUnsatisfiability, logicalConsecuence, logicalConsecuence2


# Parsing PL Formulas

@docs fplReadFromString, fplReadExtraction, fplRead, splRead, fplToInputString


# Parsing Interpretations

@docs interpretationReadFromString, interpretationReadExtraction


# Repesentation for PL Formulas

@docs fplToString, fplToMathString, fplTruthTableString, fplTruthTableMathString, fplFormTreeToString, fplFormTreeToDOT


# Representation for PL Sets

@docs splToString, splToMathString, splToMathString2, splTruthTableString, splTruthTableMathString, splCompactTruthTableString, splCompactTruthTableMathString


# Representation for Interpretations

@docs interpretationToString, interpretationsToString, interpretationToMathString, interpretationsToMathString


# Other functions

@docs interpretationsFromSymbolsAndLiterals, splConjunction, splDisjunction, splNegation

-}

--===========--
--  IMPORTS  --
--===========--

import Graph exposing (Edge, Graph, Node, NodeId)
import Graph.DOT as GDOT exposing (defaultStyles)
import List.Extra as LE
import LogicUS.PL.AuxiliarFunctions as AUX exposing (parserErrorToString)
import Parser exposing ((|.), (|=), Parser, Trailing(..))
import Set exposing (Set)



--===========--
--   TYPES   --
--===========--


{-| It is used to represent the propositional symbols of the formulas. It is recommended to use lowercase alphabetic characters using "\_ {...}" to indicate subscripts.

    -- Some examples of propositional symbols
    simpleSymbs : List PSymb
    simpleSymbs =
        [ "a", "b", "p", "q", "jhon", "marie" ]

    subindexedSymb : List PSymb
    subindexedSymb =
        [ "a_{1}", "p_{2,3}" ]

-}
type alias PSymb =
    ( String, List Int )


{-| It is used to define propositional formulas recursively. It allows defining atoms, negations, conjunctions, disjunctions, implications, equivalences, and unsatisfiable formulas.

    -- Some examples of definition of propositional formulas
    -- f1 = a → b
    f1 =
        Impl (Atom "a") (Atom "b")

    -- f2 = ¬(a ∧ b) ↔ (¬a ∨ ¬b)
    f2 =
        Equi (Neg (Conj (Atom "a") (Atom "b"))) (Disj (Neg (Atom "a")) (Neg (Atom "b")))

-}
type FormulaPL
    = Atom PSymb
    | Neg FormulaPL
    | Conj FormulaPL FormulaPL
    | Disj FormulaPL FormulaPL
    | Impl FormulaPL FormulaPL
    | Equi FormulaPL FormulaPL
    | Insat
    | Taut


{-|

    It corresponds to an Atom or a negation of an Atom

-}
type alias Literal =
    FormulaPL


{-| It is used to define sets of propositional formulas.

    -- fs = {a → b, ¬(a ∧ b) ↔ (¬a ∨ ¬b)}
    fs =
        [ f1, f2 ]

-}
type alias SetPL =
    List FormulaPL


{-| It is used to give a sparse definition of an Interpretation as a list of PSymb. This definition assumed that symbols including in the list are considered True. The rest are considered False.

    -- i1 = {a=0, b=1}
    i1 =
        [ "b" ]

    -- i2 ={a=1, b=0}
    i2 =
        [ "a" ]

    -- i3 = {a=1, b=1}
    i3 =
        [ "a", "b" ]

-}
type alias Interpretation =
    List PSymb



--===============--
--  FUNCTIONS    --
--===============--
-----------------------
-- Calc functions -
-----------------------


{-| It checks if a formula is a literal or not.

    fplIsLiteral (Atom "p\_{1}") == True
    fplIsLiteral (Neg(Atom "p\_{1}")) == True
    fplIsLiteral (Disj (Atom "p\_{1}") (Atom "p\_{2}")) == False

-}
fplIsLiteral : FormulaPL -> Bool
fplIsLiteral f =
    case f of
        Atom _ ->
            True

        Neg (Atom _) ->
            True

        _ ->
            False


{-| It checks if a formula is a positive literal or not

    fplIsPositiveLiteral (Atom "p\_{1}") == True

    fplIsPositiveLiteral (Neg(Atom "p\_{1}")) == False

    fplIsPositiveLiteral (Disj (Atom "p\_{1}") (Atom "p\_{2}")) == False

-}
fplIsPositiveLiteral : FormulaPL -> Bool
fplIsPositiveLiteral f =
    case f of
        Atom _ ->
            True

        _ ->
            False


{-| It checks if a formula is a negative literal or not

    fplIsNegativeLiteral (Atom "p\_{1}") == False

    fplIsNegativeLiteral (Neg(Atom "p\_{1}")) == True

    fplIsNegativeLiteral (Disj (Atom "p\_{1}") (Atom "p\_{2}")) == False

-}
fplIsNegativeLiteral : FormulaPL -> Bool
fplIsNegativeLiteral f =
    case f of
        Neg (Atom _) ->
            True

        _ ->
            False


{-| It gives the negation of a formula.

    fplNegation (Neg f1) == f1

    fplNegation Insat == Taut

    fplNegation f1 = Neg f1

-}
fplNegation : FormulaPL -> FormulaPL
fplNegation f =
    case f of
        Neg p ->
            p

        Insat ->
            Taut

        Taut ->
            Insat

        _ ->
            Neg f


{-| It calculates all the symbols that take place in a formula

    fplSymbols f1 == [ "a", "b" ]

    fplSymbols f2 == [ "a", "b" ]

-}
fplSymbols : FormulaPL -> List PSymb
fplSymbols f =
    List.sort <| Set.toList <| fplSymbolsAux f


fplSymbolsAux : FormulaPL -> Set PSymb
fplSymbolsAux f =
    case f of
        Atom psymb ->
            Set.singleton psymb

        Neg p ->
            fplSymbolsAux p

        Conj p q ->
            Set.union (fplSymbolsAux p) (fplSymbolsAux q)

        Disj p q ->
            Set.union (fplSymbolsAux p) (fplSymbolsAux q)

        Impl p q ->
            Set.union (fplSymbolsAux p) (fplSymbolsAux q)

        Equi p q ->
            Set.union (fplSymbolsAux p) (fplSymbolsAux q)

        Insat ->
            Set.empty

        Taut ->
            Set.empty


{-| It calculates all the symbols that take place in a set of formulas

    fplSymbols f2 == [ "a", "b" ]

-}
splSymbols : List FormulaPL -> List PSymb
splSymbols fs =
    List.sort <| Set.toList <| List.foldr (\x acc -> Set.union acc (fplSymbolsAux x)) Set.empty fs


{-| It gives a Graph.Graph with the form tree of a formula. If you want visualize it you can use formTreeHTML (defined in module Logicus.Base.Repr.SintaxSemantics.HTML) that gives a dot code of the graph. You can visualize it in a online graphviz visualizer or you can create an html file and follow the instructions (defined in Logicus.PL.Repr.Common.GraphViz).

    fplFormTree f1 == Graph.Graph (Inner { left = Inner { left = Leaf { key = 0, value = { incoming = Empty, node = { id = 0, label = Impl (Atom "a") (Atom "b") }, outgoing = Inner { left = Leaf { key = 1, value = () }, prefix = { branchingBit = 2, prefixBits = 0 }, right = Leaf { key = 2, value = () }, size = 2 } } }, prefix = { branchingBit = 1, prefixBits = 0 }, right = Leaf { key = 1, value = { incoming = Leaf { key = 0, value = () }, node = { id = 1, label = Atom "a" }, outgoing = Empty } }, size = 2 }, prefix = { branchingBit = 2, prefixBits = 0 }, right = Leaf { key = 2, value = { incoming = Leaf { key = 0, value = () }, node = { id = 2, label = Atom "b" }, outgoing = Empty } }, size = 3 })

-}
fplFormTree : FormulaPL -> Graph FormulaPL ()
fplFormTree f =
    case f of
        Atom _ ->
            Graph.fromNodesAndEdges [ Graph.Node 0 f ] []

        Neg p ->
            let
                ( nodes, edges ) =
                    fplFormTreeAux p 1
            in
            Graph.fromNodesAndEdges (Graph.Node 0 f :: nodes) (Graph.Edge 0 1 () :: edges)

        Conj p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Graph.Node 0 f :: (nodes1 ++ nodes2)) ([ Graph.Edge 0 1 (), Graph.Edge 0 nextid () ] ++ edges1 ++ edges2)

        Disj p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Graph.Node 0 f :: (nodes1 ++ nodes2)) ([ Graph.Edge 0 1 (), Graph.Edge 0 nextid () ] ++ edges1 ++ edges2)

        Impl p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Graph.Node 0 f :: (nodes1 ++ nodes2)) ([ Graph.Edge 0 1 (), Graph.Edge 0 nextid () ] ++ edges1 ++ edges2)

        Equi p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p 1
            in
            let
                nextid =
                    List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            Graph.fromNodesAndEdges (Graph.Node 0 f :: (nodes1 ++ nodes2)) ([ Graph.Edge 0 1 (), Graph.Edge 0 nextid () ] ++ edges1 ++ edges2)

        Insat ->
            Graph.fromNodesAndEdges [ Graph.Node 0 f ] []

        Taut ->
            Graph.fromNodesAndEdges [ Graph.Node 0 f ] []


fplFormTreeAux : FormulaPL -> NodeId -> ( List (Node FormulaPL), List (Edge ()) )
fplFormTreeAux f nodeid =
    case f of
        Atom _ ->
            ( [ Graph.Node nodeid f ], [] )

        Neg p ->
            let
                ( nodes, edges ) =
                    fplFormTreeAux p (nodeid + 1)
            in
            ( Graph.Node nodeid f :: nodes, Graph.Edge nodeid (nodeid + 1) () :: edges )

        Conj p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            ( Graph.Node nodeid f :: (nodes1 ++ nodes2), [ Graph.Edge nodeid (nodeid + 1) (), Graph.Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Disj p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            ( Graph.Node nodeid f :: (nodes1 ++ nodes2), [ Graph.Edge nodeid (nodeid + 1) (), Graph.Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Impl p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            ( Graph.Node nodeid f :: (nodes1 ++ nodes2), [ Graph.Edge nodeid (nodeid + 1) (), Graph.Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Equi p q ->
            let
                ( nodes1, edges1 ) =
                    fplFormTreeAux p (nodeid + 1)
            in
            let
                nextid =
                    nodeid + List.length nodes1 + 1
            in
            let
                ( nodes2, edges2 ) =
                    fplFormTreeAux q nextid
            in
            ( Graph.Node nodeid f :: (nodes1 ++ nodes2), [ Graph.Edge nodeid (nodeid + 1) (), Graph.Edge nodeid nextid () ] ++ edges1 ++ edges2 )

        Insat ->
            ( [ Graph.Node nodeid f ], [] )

        Taut ->
            ( [ Graph.Node nodeid f ], [] )


{-| It calculates the truth value of a formula regarding to an interpretation.

    fplValuation f1 i1 == True

    fplValuation f1 i2 == False

    fplValuation f2 i3 == True

-}
fplValuation : FormulaPL -> Interpretation -> Bool
fplValuation f i =
    case f of
        Atom psymb ->
            List.member psymb i

        Neg p ->
            not (fplValuation p i)

        Conj p q ->
            fplValuation p i && fplValuation q i

        Disj p q ->
            fplValuation p i || fplValuation q i

        Impl p q ->
            not (fplValuation p i) || fplValuation q i

        Equi p q ->
            fplValuation (Impl p q) i && fplValuation (Impl q p) i

        Insat ->
            Basics.False

        Taut ->
            Basics.True


{-| It calculates the list of interpretations from a list of symbols and a list of literals taking each symbol as true if it apears as positive literal,
as negative if it apears as negative literal and indiferent if it doesn't appear.
-}
interpretationsFromSymbolsAndLiterals : List PSymb -> List Literal -> List Interpretation
interpretationsFromSymbolsAndLiterals symbs literals =
    let
        symbsLiterals =
            splSymbols literals

        trueSymbs =
            List.filter (\x -> List.member (Atom x) literals) symbs
    in
    let
        optSymbs =
            AUX.powerset <| List.filter (\x -> not <| List.member x symbsLiterals) symbs
    in
    List.map (\ls -> (List.sort << LE.unique) (ls ++ trueSymbs)) optSymbs


{-| It calculates the truth value of a set of formulas regarding to an interpretation.

    splValuation fs i1 == True

    splValuation fs i2 == False

    splValuation fs i3 == True

-}
splValuation : SetPL -> Interpretation -> Bool
splValuation fs i =
    List.all (\p -> fplValuation p i) fs


{-| It gives all possible interpretations of a formula.

    fplInterpretations f1 == [ [], [ "b" ], [ "a" ], [ "a", "b" ] ]

    fplInterpretations f2 == [ [], [ "b" ], [ "a" ], [ "a", "b" ] ]

-}
fplInterpretations : FormulaPL -> List Interpretation
fplInterpretations f =
    List.sort <| List.map List.sort <| AUX.powerset <| fplSymbols f


{-| It gives all possible interpretations of a set of formulas.

    splInterpretations fs == [ [], [ "b" ], [ "a" ], [ "a", "b" ] ]

-}
splInterpretations : SetPL -> List Interpretation
splInterpretations fs =
    AUX.powerset <| splSymbols fs


{-| It gives all models of a formula

    fplModels f1 == [ [], [ "b" ], [ "a", "b" ] ]

    fplModels f2 == [ [], [ "b" ], [ "a" ], [ "a", "b" ] ]

-}
fplModels : FormulaPL -> List Interpretation
fplModels f =
    List.filter (\y -> fplValuation f y) (fplInterpretations f)


{-| It gives all countermodels of a formula

    fplCountermodels f1 == [ [ "a" ] ]

    fplCountermodels f2 == []

-}
fplCountermodels : FormulaPL -> List Interpretation
fplCountermodels f =
    List.filter (\y -> not (fplValuation f y)) (fplInterpretations f)


{-| It gives all models and countermodels of a formula as a tuple (models, countermodels).

    fplModelsCountermodels f1 == ( [ [], [ "b" ], [ "a", "b" ] ], [ [ "a" ] ] )

    fplModelsCountermodels f2 == ( [ [], [ "b" ], [ "a" ], [ "a", "b" ] ], [] )

-}
fplModelsCountermodels : FormulaPL -> ( List Interpretation, List Interpretation )
fplModelsCountermodels f =
    List.partition (\y -> fplValuation f y) (fplInterpretations f)


{-| It gives all models of a set of formulas

    splModels fs == [ [], [ "b" ], [ "a", "b" ] ]

-}
splModels : SetPL -> List Interpretation
splModels fs =
    List.filter (\y -> splValuation fs y) (splInterpretations fs)


{-| It gives all countermodels of a set of formulas

    splCountermodels fs == [ [ "a" ] ]

-}
splCountermodels : SetPL -> List Interpretation
splCountermodels fs =
    List.filter (\y -> not (splValuation fs y)) (splInterpretations fs)


{-| It gives all models and countermodels of a set of formulas as a tuple (models, countermodels).

    splModelsCountermodels fs == ( [ [], [ "b" ], [ "a", "b" ] ], [ [ "a" ] ] )

-}
splModelsCountermodels : SetPL -> ( List Interpretation, List Interpretation )
splModelsCountermodels fs =
    List.partition (\y -> splValuation fs y) (splInterpretations fs)


{-| It gives the truth table of a formula as a List(Interpretation, Bool). You cab visualize it as a table using the function fplTruthTableHTML (defined in module Logicus.Base.Repr.SintaxSemantics.HTML) or using fplTruthTableMathString (defined in module Logicus.Base.Repr.SintaxSemantics.Latex) and follow the instructions given in the respective module.

    fplTruthTable f1 == [ ( [], True ), ( [ "b" ], True ), ( [ "a" ], False ), ( [ "a", "b" ], True ) ]

    flpTruthTable f2 == [ ( [], True ), ( [ "b" ], True ), ( [ "a" ], True ), ( [ "a", "b" ], True ) ]

-}
fplTruthTable : FormulaPL -> List ( Interpretation, Bool )
fplTruthTable f =
    List.map (\x -> ( x, fplValuation f x )) (fplInterpretations f)


{-| It gives the truth table of a set of formulas as a List(Interpretation, Bool). You can visualize it as a table using the function splTruthTableHTML (defined in module Logicus.Base.Repr.SintaxSemantics.HTML) or using splTruthTableLatex (defined in module Logicus.Base.Repr.SintaxSemantics.Latex) and follow the instructions given in the respective module.

    splTruthTable fs == [ ( [], True ), ( [ "b" ], True ), ( [ "a" ], False ), ( [ "a", "b" ], True ) ]

-}
splTruthTable : SetPL -> List ( Interpretation, Bool )
splTruthTable fs =
    List.map (\x -> ( x, splValuation fs x )) (splInterpretations fs)


{-| It gives if a formula is satisfiable (bruteforce)

    fplSatisfiability f1 == True

    fplSatisfiability f2 == True

-}
fplSatisfiability : FormulaPL -> Bool
fplSatisfiability f =
    List.any (\x -> fplValuation f x) (fplInterpretations f)


{-| It gives if a formula is a tautology (bruteforce)

    fplValidity f1 == False

    fplValidity f2 == True

-}
fplValidity : FormulaPL -> Bool
fplValidity f =
    List.all (\x -> fplValuation f x) (fplInterpretations f)


{-| It gives if a formula is unsatisfiable (bruteforce)

    fplUnsatisfiability f1 == False

    fplUnsatisfiability f2 == False

    fplUnsatisfiability Insat == True

-}
fplUnsatisfiability : FormulaPL -> Bool
fplUnsatisfiability f =
    List.all (\x -> not (fplValuation f x)) (fplInterpretations f)


{-| It gives if a set of formulas is satisfiable (bruteforce)

    splSatisfiability fs == True

    splSatisfiability (fs ++ [ Atom "a", Neg (Atom "b") ]) == False

-}
splSatisfiability : SetPL -> Bool
splSatisfiability fs =
    List.any (\x -> splValuation fs x) (splInterpretations fs)


{-| It gives if a set of formulas is unsatisfiable (bruteforce)

    splUnsatisfiability fs == False

    splUnatisfiability (fs ++ [ Atom "a", Neg (Atom "b") ]) == True

-}
splUnsatisfiability : SetPL -> Bool
splUnsatisfiability fs =
    List.all (\x -> not (splValuation fs x)) (splInterpretations fs)


{-| It gives if a if a formula F is consecuence of a set of formulas S checking if S U {F} is unsatisfiable. (bruteforce)

    logicalConsecuence2 fs (Disj (Neg (Atom "a")) (Atom "b")) == True

    logicalConsecuence2 fs Insat == False

    logicalConsecuence2 [ Insat ] f1 == True -- You can deduce anything of an unsatifiable set.

-}
logicalConsecuence2 : SetPL -> FormulaPL -> Bool
logicalConsecuence2 fs f =
    splUnsatisfiability (fs ++ [ Neg f ])


{-| It gives if a if a formula F is consecuence of a set of formulas S checking if all model of S is also model of F. (bruteforce)

    logicalConsecuence fs (Disj (Neg (Atom "a")) (Atom "b")) == True

    logicalConsecuence fs Insat == False

    logicalConsecuence [ Insat ] f1 == True -- You can deduce anything of an unsatifiable set.

-}
logicalConsecuence : SetPL -> FormulaPL -> Bool
logicalConsecuence fs f =
    -- The interpretations must range over the symbols of F too: a symbol that only
    -- occurs in F can take either value in a model of S.
    splInterpretations (f :: fs)
        |> List.filter (splValuation fs)
        |> List.all (fplValuation f)



-----------------------
--  Parser functions  -
-----------------------


{-| It reads the formula from a string.It returns a tuple with may be a formula (if it can be read it), the input considerated to parse and a message of error it it is not able to performs the parsing.

The string must satisfy the following rules:

  - Propositional variables must correspond to strings of lowercase characters indexed, optionally, by a series of indices, corresponding to integers, specified between the symbols `_{` and `}` and separated by commas. Examples of valid propositional variables are `p`, `p_{1}`, `p_{1,2,3}`, `p_{1,2,3}`, `p_{1,2,3}` and `p_{1}`.

  - The unitary negation connective is represented by the symbol `¬` (Alt Gr + 6) and is used prefixed (as in formalism) while the binary connectives are used infixed (as in formalism) and are represented by the following symbols: `&` (conjunction), `|` (disjunction), `->` (implication) and `<->` (equivalence). So examples of definition with connectives are : `p -> q`, `p_{1} & p_{2} -> p_{1} | p_{2}`, `p -> q <-> p | q`.

  - In case of the same connective, it will be associated from the right, although it is advisable to use the brackets `(`...`)` as special symbols that allow altering the priority of the connectives by explicitly establishing the order of association. For example `¬(p -> q) | r & s)`.

  - The inconsistent formula is represented by the symbol `!F` and the valid formula by the symbol `!T`.

  - The use of spaces is irrelevant.

```
fplReadFromString "p" == ( Just (Atom "p"), "p", "" )

fplReadFromString "p_{1} & p_{2}" == ( Just (Conj (Atom "p_{1}") (Atom "p_{2}")), "(p_{1}&p_{2})", "" )

fplReadFromString "(p | q -> r)" == ( Just (Impl (Disj (Atom "p") (Atom "q")) (Atom "r")), "((p|q)->r)", "" )

fplReadFromString "p_{1,1} <-> p_{1,2}" == ( Just (Equi (Atom "p_{1,1}") (Atom "p_{1,2}")), "(p_{1,1}<->p_{1,2})", "" )

fplReadFromString "!F" == ( Just Insat, "!F", "" )

fplReadFromString "p_1" == ( Nothing, "(p_1)", "Error: [{ col = 3, problem = ExpectingSymbol ')', row = 1 }]" )
```

Messages are not perfect but we're working to improve it.

-}
fplReadFromString : String -> ( Maybe FormulaPL, String, String )
fplReadFromString x =
    case AUX.cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "", "Argument is empty" )

        s ->
            case Parser.run fplParser ("(" ++ s ++ ")") of
                Ok y ->
                    ( Maybe.Just y, fplToInputString y, "" )

                Err y ->
                    ( Maybe.Nothing, "(" ++ s ++ ")", parserErrorToString ("(" ++ s ++ ")") 1 y )


{-| It extract the formula readed. If it is Nothing it returns Insat

    f3 = fplReadExtraction <| fplReadFromString "(p | q -> r)"
    f3 == Impl (Disj (Atom "p") (Atom "q")) (Atom "r")
    f4 = fplReadExtraction <| fplReadFromString "(p | q <- r)"
    f4 == Insat

-}
fplReadExtraction : ( Maybe FormulaPL, String, String ) -> FormulaPL
fplReadExtraction ( fpl, _, _ ) =
    Maybe.withDefault Insat fpl


{-| It reads the formula from a string. It returns the Formula if the string si correct, otherwise it returns Insat.
-}
fplRead : String -> FormulaPL
fplRead =
    fplReadExtraction << fplReadFromString


{-| It reads a set of formulas from a string. Each string that corresponds to each of the formulas of the set must be ended by a point `.`
(the last formula can, optionally, not be ended by a point).
-}
splRead : String -> SetPL
splRead fs =
    let
        fsRead =
            List.map fplReadFromString <| List.filter (not << String.isEmpty << AUX.cleanSpaces) <| String.split "." fs
    in
    if List.any (\( mf, _, _ ) -> mf == Nothing) fsRead then
        []

    else
        List.map fplReadExtraction fsRead


{-| It gives the corresponding input syntax of a formula

    fplToInputString f3 == "((p|q)->r)"

    fplToInputString f4 == "!F"

-}
fplToInputString : FormulaPL -> String
fplToInputString f =
    case f of
        Atom ( vname, [] ) ->
            (String.toLower << String.left 1) vname ++ String.dropLeft 1 vname

        Atom ( vname, vindices ) ->
            (String.toLower << String.left 1) vname ++ String.dropLeft 1 vname ++ "_{" ++ (String.join "," <| List.map String.fromInt vindices) ++ "}"

        Neg p ->
            "¬" ++ fplToInputString p

        Conj p q ->
            "(" ++ fplToInputString p ++ "&" ++ fplToInputString q ++ ")"

        Disj p q ->
            "(" ++ fplToInputString p ++ "|" ++ fplToInputString q ++ ")"

        Impl p q ->
            "(" ++ fplToInputString p ++ "->" ++ fplToInputString q ++ ")"

        Equi p q ->
            "(" ++ fplToInputString p ++ "<->" ++ fplToInputString q ++ ")"

        Insat ->
            "!F"

        Taut ->
            "!T"



-- PARSER BUIDER FUCTIONS
-- It defines the syntax of a propositional variable that can be subscripting or not


plVarParser : Parser ( String, List Int )
plVarParser =
    Parser.oneOf
        [ Parser.succeed identity
            |= Parser.backtrackable plVarIdentifierSubindexedParser
        , Parser.succeed (\x -> ( x, [] ))
            |= plVarNameParser
        ]


plVarNameParser : Parser String
plVarNameParser =
    Parser.succeed ()
        |. Parser.chompIf Char.isAlphaNum
        |. Parser.chompWhile Char.isAlphaNum
        |> Parser.getChompedString


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



-- It defines the propositional infixed operators (and, or, implication and equivalence)


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



-- It defines the syntax of formulas and its processing enusuring that it corresponds to the parser of all of the string given.


fplParser : Parser FormulaPL
fplParser =
    Parser.succeed identity
        |= fplParserAux
        |. Parser.oneOf [
            Parser.symbol "."
            ,Parser.end
        ]
         


fplParserAux : Parser FormulaPL
fplParserAux =
    Parser.oneOf
        [ Parser.succeed identity
            |. Parser.symbol "("
            |= Parser.lazy (\_ -> expression)
            |. Parser.symbol ")"
        , Parser.succeed Neg
            |. Parser.oneOf
                [ Parser.symbol "¬"
                , Parser.symbol "-"
                ]
            |= Parser.lazy (\_ -> fplParserAux)
        , Parser.succeed Insat
            |. Parser.symbol "!F"
        , Parser.succeed Insat
            |. Parser.symbol "⊥"
        , Parser.succeed Taut
            |. Parser.symbol "!T"
        , Parser.succeed Taut
            |. Parser.symbol "⊤"
        , Parser.succeed Atom
            |= plVarParser
        ]


expression : Parser FormulaPL
expression =
    fplParserAux |> Parser.andThen (expressionAux [])


expressionAux : List ( FormulaPL, Operator ) -> FormulaPL -> Parser FormulaPL
expressionAux revOps expr =
    Parser.oneOf
        [ Parser.succeed Tuple.pair
            |= operator
            |= fplParserAux
            |> Parser.andThen (\( op, newExpr ) -> expressionAux (( expr, op ) :: revOps) newExpr)
        , Parser.lazy (\_ -> Parser.succeed (finalize revOps expr))
        ]



-- It defines the priority and the processing of the operators and formulas.


finalize : List ( FormulaPL, Operator ) -> FormulaPL -> FormulaPL
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


{-| It reads an interpretation from a string that represents the list of propositional variables (following the rules given in `fplReadFromString` function) separated by commas and surrounded by `[` at the beginning and `]` at the end.
-}
interpretationReadFromString : String -> ( Maybe Interpretation, String )
interpretationReadFromString x =
    case AUX.cleanSpaces x of
        "" ->
            ( Maybe.Nothing, "Argument is empty" )

        s ->
            case Parser.run interpretationParser s of
                Ok y ->
                    ( (Maybe.Just << Set.toList << Set.fromList) y, "" )

                Err y ->
                    ( Maybe.Nothing, parserErrorToString s 0 y )


{-| It extract the interpretation readed. If it is Nothing it returns an empty list (all vars taking as false).
-}
interpretationReadExtraction : ( Maybe Interpretation, String ) -> Interpretation
interpretationReadExtraction ( x, _ ) =
    Maybe.withDefault [] x



-- Parser for reading interpretations


interpretationParser : Parser Interpretation
interpretationParser =
    Parser.sequence
        { start = "["
        , separator = ","
        , end = "]"
        , spaces = Parser.spaces
        , item = plVarParser
        , trailing = Forbidden
        }



-----------------------
--   Repr functions   -
-----------------------


{-| It generates the String representation of a PL formula using unicode symbols.

    fplToString f1 == "( a → b )"

    fplToString f2 == "( ¬ ( a ∧ b ) ↔ ( ¬ a ∨ ¬ b ) )"

-}
fplToString : FormulaPL -> String
fplToString f =
    case f of
        Atom ( pname, [] ) ->
            pname

        Atom ( pname, pindices ) ->
            pname ++ (AUX.replaceBySubscript <| (String.join "," <| List.map String.fromInt pindices))

        Neg p ->
            case p of
                Conj _ _ ->
                    "¬ (" ++ fplToString p ++ ")"

                Disj _ _ ->
                    "¬ (" ++ fplToString p ++ ")"

                Impl _ _ ->
                    "¬ (" ++ fplToString p ++ ")"

                Equi _ _ ->
                    "¬ (" ++ fplToString p ++ ")"

                _ ->
                    "¬ " ++ fplToString p

        Conj p q ->
            let
                lhs =
                    case p of
                        Disj _ _ ->
                            "(" ++ fplToString p ++ ")"

                        Impl _ _ ->
                            "(" ++ fplToString p ++ ")"

                        Equi _ _ ->
                            "(" ++ fplToString p ++ ")"

                        _ ->
                            fplToString p

                rhs =
                    case q of
                        Disj _ _ ->
                            "(" ++ fplToString q ++ ")"

                        Impl _ _ ->
                            "(" ++ fplToString q ++ ")"

                        Equi _ _ ->
                            "(" ++ fplToString q ++ ")"

                        _ ->
                            fplToString q
            in
            lhs ++ " ∧ " ++ rhs

        Disj p q ->
            let
                lhs =
                    case p of
                        Impl _ _ ->
                            "(" ++ fplToString p ++ ")"

                        Equi _ _ ->
                            "(" ++ fplToString p ++ ")"

                        _ ->
                            fplToString p

                rhs =
                    case q of
                        Impl _ _ ->
                            "(" ++ fplToString q ++ ")"

                        Equi _ _ ->
                            "(" ++ fplToString q ++ ")"

                        _ ->
                            fplToString q
            in
            lhs ++ " ∨ " ++ rhs

        Impl p q ->
            let
                lhs =
                    case p of
                        Impl _ _ ->
                            "(" ++ fplToString p ++ ")"

                        Equi _ _ ->
                            "(" ++ fplToString p ++ ")"

                        _ ->
                            fplToString p

                rhs =
                    case q of
                        Equi _ _ ->
                            "(" ++ fplToString q ++ ")"

                        _ ->
                            fplToString q
            in
            lhs ++ " → " ++ rhs

        Equi p q ->
            let
                lhs =
                    case p of
                        Equi _ _ ->
                            "(" ++ fplToString p ++ ")"

                        _ ->
                            fplToString p

                rhs =
                    case q of
                        _ ->
                            fplToString q
            in
            lhs ++ " ↔ " ++ rhs

        Insat ->
            "⊥"

        Taut ->
            "⊤"


{-| It generates the Latex string of a PL formula. The result requires a math enviroment to be displayed.

    fplToMathString f1 == "( a\\rightarrow b )"

    fplToMathString f2 == "( \\neg ( a \\wedge b ) \\leftrightarrow ( \\neg a \\vee \\neg b ) )"

-}
fplToMathString : FormulaPL -> String
fplToMathString f =
    case f of
        Atom ( pname, [] ) ->
            pname

        Atom ( pname, pindices ) ->
            pname ++ "_{" ++ (String.join "," <| List.map String.fromInt pindices) ++ "}"

        Neg p ->
            case p of
                Conj _ _ ->
                    " \\neg \\left( " ++ fplToMathString p ++ " \\right) "

                Disj _ _ ->
                    " \\neg \\left( " ++ fplToMathString p ++ " \\right) "

                Impl _ _ ->
                    " \\neg \\left( " ++ fplToMathString p ++ " \\right) "

                Equi _ _ ->
                    " \\neg \\left( " ++ fplToMathString p ++ " \\right) "

                _ ->
                    " \\neg " ++ fplToMathString p

        Conj p q ->
            let
                lhs =
                    case p of
                        Disj _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        Impl _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        Equi _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        _ ->
                            fplToMathString p

                rhs =
                    case q of
                        Disj _ _ ->
                            " \\left( " ++ fplToMathString q ++ " \\right) "

                        Impl _ _ ->
                            " \\left( " ++ fplToMathString q ++ " \\right) "

                        Equi _ _ ->
                            " \\left( " ++ fplToMathString q ++ " \\right) "

                        _ ->
                            fplToMathString q
            in
            lhs ++ " \\wedge " ++ rhs

        Disj p q ->
            let
                lhs =
                    case p of
                        Impl _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        Equi _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        _ ->
                            fplToMathString p

                rhs =
                    case q of
                        Impl _ _ ->
                            " \\left( " ++ fplToMathString q ++ " \\right) "

                        Equi _ _ ->
                            " \\left( " ++ fplToMathString q ++ " \\right) "

                        _ ->
                            fplToMathString q
            in
            lhs ++ " \\vee " ++ rhs

        Impl p q ->
            let
                lhs =
                    case p of
                        Impl _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        Equi _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        _ ->
                            fplToMathString p

                rhs =
                    case q of
                        Equi _ _ ->
                            " \\left( " ++ fplToMathString q ++ " \\right) "

                        _ ->
                            fplToMathString q
            in
            lhs ++ " \\rightarrow " ++ rhs

        Equi p q ->
            let
                lhs =
                    case p of
                        Equi _ _ ->
                            " \\left( " ++ fplToMathString p ++ " \\right) "

                        _ ->
                            fplToMathString p

                rhs =
                    case q of
                        _ ->
                            fplToMathString q
            in
            lhs ++ " \\leftrightarrow " ++ rhs

        Insat ->
            " \\perp "

        Taut ->
            " \\top "


{-| It generates the String of Set of PL formulas using unicode symbols.

    splToString [ f1, f2 ] == "{( a → b ), ( ¬ ( a ∧ b ) ↔ ( ¬ a ∨ ¬ b ) )}"

-}
splToString : SetPL -> String
splToString fs =
    "{" ++ (String.join ", " <| List.map fplToString fs) ++ "}"


{-| It generates the Latex string of a Set of PL formulas. The result requires a math enviroment to be displayed.

    splToMathString [ f1, f2 ] == "\\lbrace ( a\\rightarrow b ), ( \\neg ( a \\wedge b )\\leftrightarrow ( \\neg a \\vee \\neg b ) )\\rbrace"

-}
splToMathString : List FormulaPL -> String
splToMathString fs =
    "\\begin{array}{c} " ++ (String.join " \\\\ " <| List.map fplToMathString fs) ++ "\\end{array}"


{-| It generates the Latex string of a Set of PL formulas in one line, avoiding the use of the array. The result requires a math enviroment to be displayed.
-}
splToMathString2 : List FormulaPL -> String
splToMathString2 fs =
    "\\lbrace " ++ (String.join ", \\, " <| List.map fplToMathString fs) ++ "\\rbrace"


{-| It generates the Truth Table of a PL formula as a string using CSV format (separated by ';')

    fplTruthTableString f1 == "a ; b ; ( a → b ) \nF ; F ; T \nF ; T ; T \nT ; F ; F \nT ; T ; T""
    fplTruthTableString f2 == "a ; b ; ( ¬ ( a ∧ b ) ↔ ( ¬ a ∨ ¬ b ) ) \nF ; F ; T \nF ; T ; T \nT ; F ; T \nT ; T ; T"

-}
fplTruthTableString : FormulaPL -> String
fplTruthTableString f =
    let
        tableEnters =
            fplTruthTable f

        symbs =
            fplSymbols f
    in
    let
        head =
            List.map (fplToString << Atom) symbs ++ [ fplToString f ]

        body =
            List.map
                (\( i, v ) ->
                    List.map
                        (\s ->
                            if List.member s i then
                                "T"

                            else
                                "F"
                        )
                        symbs
                        ++ [ if v then
                                "T"

                             else
                                "F"
                           ]
                )
                tableEnters
    in
    AUX.fromListToTableString (head :: body)


{-| It generates the Latex code of a Truth Table of a PL formula. The result requires a math enviroment to be displayed.

    fplTruthTableMathString f1 == "\\begin{array}{c|c|c|}\n\mathbf{a} & \\mathbf{b} & \\mathbf{( a\\rightarrow b )} \\\\ \\hline \nF & F & T \\\\ \nF & T & T \\\\ \nT & F & F \\\\ \nT & T & T \\\\ \\end{array}"

    fplTruthTableMathString f2 == "\\begin{array}{c|c|c|}\n\n\\mathbf{a} & \\mathbf{b} & \\mathbf{( \\neg ( a \\wedge b )\\leftrightarrow ( \\neg a \\vee \\neg b ) )} \\\\\\hlineF & F & T \\\\ \nF & T & T \\\\ \nT & F & T \\\\ \nT & T & T \\\\ \\end{array}"

-}
fplTruthTableMathString : FormulaPL -> String
fplTruthTableMathString f =
    let
        tableEnters =
            fplTruthTable f

        symbs =
            fplSymbols f
    in
    let
        head =
            List.map (fplToMathString << Atom) symbs ++ [ fplToMathString f ]

        body =
            List.map
                (\( i, v ) ->
                    List.map
                        (\s ->
                            if List.member s i then
                                "T"

                            else
                                "F"
                        )
                        symbs
                        ++ [ if v then
                                "T"

                             else
                                "F"
                           ]
                )
                tableEnters
    in
    AUX.fromListToTableLatex ("|" ++ String.repeat (List.length symbs + 1) "c|") [ head ] body []


{-| It generates the Truth Table of a set of PL formulas as a string using CSV format.

    splTruthTableString [ f1, f2 ] == "a ; b ; ( a → b ) ; ( ¬ ( a ∧ b ) ↔ ( ¬ a ∨ ¬ b ) ) ; U \n0 ; 0 ; T ; T ; T \n0 ; 1 ; T ; T ; T \n1 ; 0 ; F ; T ; F \n1 ; 1 ; T ; T ; T"

-}
splTruthTableString : SetPL -> String
splTruthTableString fs =
    let
        tableEnters =
            splTruthTable fs

        symbs =
            splSymbols fs
    in
    let
        head =
            List.map (fplToString << Atom) symbs ++ List.map fplToString fs ++ [ "U" ]

        body =
            List.map
                (\( i, v ) ->
                    List.map
                        (\s ->
                            if List.member s i then
                                "T"

                            else
                                "F"
                        )
                        symbs
                        ++ List.map
                            (\p ->
                                if fplValuation p i then
                                    "T"

                                else
                                    "F"
                            )
                            fs
                        ++ [ if v then
                                "T"

                             else
                                "F"
                           ]
                )
                tableEnters
    in
    AUX.fromListToTableString (head :: body)


{-| It generates the Truth Table of a set of PL formulas as a string using CSV format. It only shows the truth values of variables and the evaluation of the set.
-}
splCompactTruthTableString : SetPL -> String
splCompactTruthTableString fs =
    let
        tableEnters =
            splTruthTable fs

        symbs =
            splSymbols fs
    in
    let
        head =
            List.map (fplToString << Atom) symbs ++ [ "U" ]

        body =
            List.map
                (\( i, v ) ->
                    List.map
                        (\s ->
                            if List.member s i then
                                "T"

                            else
                                "F"
                        )
                        symbs
                        ++ [ if v then
                                "T"

                             else
                                "F"
                           ]
                )
                tableEnters
    in
    AUX.fromListToTableString (head :: body)


{-| It generates the Latex code of a Truth Table of Set of PL formulas. The result requires a math enviroment to be displayed.

    splTruthTableMathString [ f1, f2 ] =
        "\\begin{array}{c|c|c|c|c|}\\mathbf{a} & \\mathbf{b} & \\mathbf{( a \\rightarrow b )} & \\mathbf{( \\neg ( a \\wedge b ) \\leftrightarrow ( \\neg a \\vee \\neg b ) )} & \\mathbf{U} \\\\ \\hlineF & F & T & T & T \\\\ F & T & T & T & T \\\\ T & F & F & T & F \\\\ T & T & T & T & T \\\\ \\end{array}"

-}
splTruthTableMathString : SetPL -> String
splTruthTableMathString fs =
    let
        tableEnters =
            splTruthTable fs

        symbs =
            splSymbols fs
    in
    let
        head =
            List.map (fplToMathString << Atom) symbs ++ List.map fplToMathString fs ++ [ "U" ]

        body =
            List.map
                (\( i, v ) ->
                    List.map
                        (\s ->
                            if List.member s i then
                                "T"

                            else
                                "F"
                        )
                        symbs
                        ++ List.map
                            (\p ->
                                if fplValuation p i then
                                    "T"

                                else
                                    "F"
                            )
                            fs
                        ++ [ if v then
                                "T"

                             else
                                "F"
                           ]
                )
                tableEnters
    in
    AUX.fromListToTableLatex ("|" ++ String.repeat (List.length symbs + List.length fs + 1) "c|") [ head ] body []


{-| It generates the Latex code of a Truth Table of Set of PL formulas. It only shows the truth values of the variables and the evaluation of the set. The result requires a math enviroment to be displayed.
-}
splCompactTruthTableMathString : SetPL -> String
splCompactTruthTableMathString fs =
    let
        tableEnters =
            splTruthTable fs

        symbs =
            splSymbols fs
    in
    let
        head =
            List.map (fplToMathString << Atom) symbs ++ [ "U" ]

        body =
            List.map
                (\( i, v ) ->
                    List.map
                        (\s ->
                            if List.member s i then
                                "T"

                            else
                                "F"
                        )
                        symbs
                        ++ [ if v then
                                "T"

                             else
                                "F"
                           ]
                )
                tableEnters
    in
    AUX.fromListToTableLatex ("|" ++ String.repeat (List.length symbs + 1) "c|") [ head ] body []


{-| It gives the String representation of a formTree.

    fplFormTreeToString <| fplFormTree f3 == "0 ( ( p ∨ q ) → r )\n1 ( p ∨ q )\n2 p\n3 q\n4 r\n#\n0 1\n0 4\n1 2\n1 3"

-}
fplFormTreeToString : Graph FormulaPL () -> String
fplFormTreeToString ftree =
    Graph.toString (\x -> Just (fplToString x)) (\_ -> Nothing) ftree


{-| It generates the formation tree of a formula as DOT string. It requires a GraphViz interpreter to be displayed.

    fplFormTreeToDOT <| fplFormTree f3 == "digraph G {\n  rankdir=TB\n  graph []\n  node [shape=plaintext, color=black]\n  edge [dir=none]\n\n  0 -> 1\n  0 -> 4\n  1 -> 2\n  1 -> 3\n\n  0 [label=\"( ( p ∨ q ) → r )\"]\n  1 [label=\"( p ∨ q )\"]\n  2 [label=\"p\"]\n  3 [label=\"q\"]\n  4 [label=\"r\"]\n}"

-}
fplFormTreeToDOT : Graph FormulaPL () -> String
fplFormTreeToDOT ftree =
    let
        myStyles =
            { defaultStyles | node = "shape=plaintext, color=black", edge = "dir=none" }
    in
    String.replace "\n" "" <| String.replace "\"" ">" <| String.replace "=\"" "=<" <| GDOT.outputWithStyles myStyles (\x -> Just (fplToString x)) (\_ -> Nothing) ftree


{-| It gives a interpretation as a string.

     interpretationToString ["a"] ["a", "b"] == "{a:T, b:F}"

-}
interpretationToString : Interpretation -> List PSymb -> String
interpretationToString i xs =
    "{"
        ++ (String.join ", " <|
                List.map
                    (\x ->
                        (fplToString << Atom) x
                            ++ ":"
                            ++ (if List.member x i then
                                    "T"

                                else
                                    "F"
                               )
                    )
                    xs
           )
        ++ "}"


{-| It gives a interpretation list as a string.

    interpretationsToString [ [], [ "a" ], [ "a", "b" ] ] [ "a", "b", "c" ]
        == "{{a:F, b:F, c:F}\n{a:T, b:F, c:F}\n{a:T, b:T, c:F}}"

-}
interpretationsToString : List Interpretation -> List PSymb -> String
interpretationsToString is xs =
    "{" ++ (String.join ", " <| List.map (\i -> interpretationToString i xs) is) ++ "}"


{-| It gives a interpretation as a string in latex format.

    interpretationToMathString [ "a" ] [ "a", "b" ] == "\\lbrace a:T, b:F \\rbrace"

-}
interpretationToMathString : Interpretation -> List PSymb -> String
interpretationToMathString i xs =
    "\\lbrace "
        ++ (String.join ", " <|
                List.map
                    (\x ->
                        (fplToMathString << Atom) x
                            ++ ":"
                            ++ (if List.member x i then
                                    "T"

                                else
                                    "F"
                               )
                    )
                    xs
           )
        ++ " \\rbrace"


{-| It gives a interpretation list as a string in latex format.

    interpretationsToMathString [ [], [ "a" ], [ "a", "b" ] ] [ "a", "b", "c" ]
        == "\\begin{array}{c}\\lbrace a:F, b:F, c:F \\rbrace \\\\ \\lbrace a:T, b:F, c:F \\rbrace \\\\ \\lbrace a:T, b:T, c:F \\rbrace \\end{array}"

-}
interpretationsToMathString : List Interpretation -> List PSymb -> String
interpretationsToMathString is xs =
    "\\begin{array}{c}" ++ (String.join " \\\\ " <| List.map (\i -> interpretationToMathString i xs) is) ++ " \\end{array}"


{-| It transforms a SetPL into a new SetPL by negating each formula of the set.
-}
splNegation : SetPL -> SetPL
splNegation =
    List.map fplNegation


{-| It transforms a SetPL into a FormulaPL using conjuction between formulas. If Set is empty Taut is given
-}
splConjunction : SetPL -> FormulaPL
splConjunction fs =
    case fs of
        [] ->
            Taut

        x :: xs ->
            List.foldl (\f ac -> Conj ac f) x xs


{-| It transforms a SetPL into a FormulaPL using disjunction between formulas. If Set is empty Insat is given
-}
splDisjunction : SetPL -> FormulaPL
splDisjunction fs =
    case fs of
        [] ->
            Insat

        x :: xs ->
            List.foldl (\f ac -> Disj ac f) x xs
