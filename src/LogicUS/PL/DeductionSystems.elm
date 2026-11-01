module LogicUS.PL.DeductionSystems exposing
    ( Preset, presets, presetSystem
    , naturalDeduction, intuitionisticRules, classicalRules, derivedRules, axiomatic
    )

{-| Deduction systems for propositional logic ready to use with `LogicUS.PL.Deduction`, as text that can be edited:
rules can be removed, renamed or added before reading it with `readSystem`.


# Presets

@docs Preset, presets, presetSystem


# Rules

@docs naturalDeduction, intuitionisticRules, classicalRules, derivedRules, axiomatic

-}

import LogicUS.PL.Deduction as D exposing (System)


{-| A system with a name and a short description.
-}
type alias Preset =
    { name : String
    , description : String
    , rules : String
    }


{-| The rules of natural deduction for the connectives that hold intuitionistically (introduction and elimination
of ∧, ∨, →, ↔, ¬ and ⊥), and reiteration.
-}
intuitionisticRules : String
intuitionisticRules =
    String.join "\n"
        [ "rule ∧I : A, B ⊢ A ∧ B"
        , "rule ∧E1 : A ∧ B ⊢ A"
        , "rule ∧E2 : A ∧ B ⊢ B"
        , "rule ∨I1 : A ⊢ A ∨ B"
        , "rule ∨I2 : B ⊢ A ∨ B"
        , "rule ∨E : A ∨ B, [A] C, [B] C ⊢ C"
        , "rule →I : [A] B ⊢ A → B"
        , "rule →E : A → B, A ⊢ B"
        , "rule ↔I : [A] B, [B] A ⊢ A ↔ B"
        , "rule ↔E1 : A ↔ B, A ⊢ B"
        , "rule ↔E2 : A ↔ B, B ⊢ A"
        , "rule ¬I : [A] ⊥ ⊢ ¬A"
        , "rule ¬E : A, ¬A ⊢ ⊥"
        , "rule ⊥E : ⊥ ⊢ A"
        , "rule R : A ⊢ A"
        ]


{-| The classical rules: elimination of the double negation and reduction to the absurd.
-}
classicalRules : String
classicalRules =
    String.join "\n"
        [ "rule ¬¬E : ¬¬A ⊢ A"
        , "rule RAA : [¬A] ⊥ ⊢ A"
        ]


{-| Classical natural deduction: the intuitionistic and the classical rules.
-}
naturalDeduction : String
naturalDeduction =
    String.join "\n\n" [ intuitionisticRules, classicalRules ]


{-| Rules that can be derived from the others, for exercises that allow them: modus tollens, disjunctive and
hypothetical syllogisms, introduction of the double negation, excluded middle and De Morgan laws.
-}
derivedRules : String
derivedRules =
    String.join "\n"
        [ "rule MT : A → B, ¬B ⊢ ¬A"
        , "rule DS : A ∨ B, ¬A ⊢ B"
        , "rule HS : A → B, B → C ⊢ A → C"
        , "rule ¬¬I : A ⊢ ¬¬A"
        , "axiom LEM : A ∨ ¬A"
        , "rule DeM1 : ¬(A ∧ B) ⊢ ¬A ∨ ¬B"
        , "rule DeM2 : ¬(A ∨ B) ⊢ ¬A ∧ ¬B"
        , "rule DeM3 : ¬A ∨ ¬B ⊢ ¬(A ∧ B)"
        , "rule DeM4 : ¬A ∧ ¬B ⊢ ¬(A ∨ B)"
        ]


{-| An axiomatic system (Łukasiewicz): three axiom schemes and modus ponens.
-}
axiomatic : String
axiomatic =
    String.join "\n"
        [ "axiom A1 : A → (B → A)"
        , "axiom A2 : (A → (B → C)) → ((A → B) → (A → C))"
        , "axiom A3 : (¬A → ¬B) → (B → A)"
        , "rule MP : A, A → B ⊢ B"
        ]


{-| The systems of this module. `LogicUS.FOL.DeductionSystems` has their first-order versions, with the same names.
-}
presets : List Preset
presets =
    [ { name = "Natural deduction (classical)", description = "Introduction and elimination rules of the connectives, ¬¬E and RAA", rules = naturalDeduction }
    , { name = "Natural deduction (intuitionistic)", description = "Without ¬¬E and RAA", rules = intuitionisticRules }
    , { name = "Natural deduction with derived rules", description = "Classical natural deduction plus MT, DS, HS, ¬¬I, LEM and De Morgan laws", rules = String.join "\n\n" [ naturalDeduction, derivedRules ] }
    , { name = "Axiomatic system", description = "Łukasiewicz's axioms A1-A3 and modus ponens", rules = axiomatic }
    ]


{-| The system of a preset, by name.
-}
presetSystem : String -> Maybe System
presetSystem name =
    presets
        |> List.filter (\p -> p.name == name)
        |> List.head
        |> Maybe.andThen (\p -> Result.toMaybe (D.readSystem p.rules))
