{-# OPTIONS --safe --without-K #-}

module CategoryAction.ContravariantAction where

open import Agda.Primitive renaming
  ( Level to Universe
  ; _⊔_   to _uMax_
  ; lsuc  to uSuc
  ; Set   to Type )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘′_; id)

open import CategoryAction.Category
open import CategoryAction.Equivalence
open import CategoryAction.Action

private
  variable
    u w o m a : Universe
    A B C : Type u

-- Contravariant from Functional Programming
record Contravariant (F : Type u -> Type u) : Type (uSuc u) where
  field
    contramap : ∀ {A B : Type u} -> (B -> A) -> F A -> F B
    -- laws
    contramap-id : ∀ {A : Type u} -> (fa : F A) ->
      contramap id fa ≡ fa
    contramap-comp : ∀ {A B C : Type u} (g : B -> A) (f : C -> B)
     (fa : F A) ->
      contramap (g ∘′ f) fa ≡ contramap f (contramap g fa)

open Action
open Contravariant

-- Contravariant ≃ Action of the opposite category

Contravariant->Action : {F : Type u -> Type u}
  -> Contravariant F -> Action OppositeFunctionCategory F
Contravariant->Action contravariant = record
  { act      = contramap contravariant
  ; act-id   = contramap-id contravariant
  ; act-comp = contramap-comp contravariant }

Action->Contravariant : ∀ {F : Type u -> Type u}
  -> Action OppositeFunctionCategory F -> Contravariant F
Action->Contravariant action = record
  { contramap      = act action
  ; contramap-id   = act-id action
  ; contramap-comp = act-comp action }

Contravariant-Action-roundtrip : ∀ {F : Type u -> Type u}
  -> (act : Action OppositeFunctionCategory F)
  -> Contravariant->Action (Action->Contravariant act) ≡ act
Contravariant-Action-roundtrip act = refl

Action-Contravariant-roundtrip : ∀ {F : Type u -> Type u}
  -> (contra : Contravariant F)
  -> Action->Contravariant (Contravariant->Action contra) ≡ contra
Action-Contravariant-roundtrip contra = refl

Contravariant≃Action : {F : Type u -> Type u}
  -> Contravariant F ≃ Action OppositeFunctionCategory F
Contravariant≃Action = record
  { to   = Contravariant->Action
  ; from = Action->Contravariant
  ; to-from = Contravariant-Action-roundtrip
  ; from-to = Action-Contravariant-roundtrip }
