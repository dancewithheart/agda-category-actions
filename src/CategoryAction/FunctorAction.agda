{-# OPTIONS --safe --without-K #-}

module CategoryAction.FunctorAction where

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

-- Functor from Functional Programming
record Functor {u : Universe} (F : Type u -> Type u) : Type (uSuc u) where
  field
    fmap : ∀ {A B : Type u} -> (A -> B) -> F A -> F B
    -- laws
    fmap-id : ∀ {A : Type u} -> (fa : F A) ->
      fmap id fa ≡ fa
    fmap-comp : ∀ {A B C : Type u} (f : A -> B) (g : B -> C) (fa : F A) ->
      fmap (g ∘′ f) fa ≡ fmap g (fmap f fa)

open Functor
open Action

-- Functor ≃ Action of the function category

Functor->Action : ∀ {F : Type u -> Type u}
  -> Functor F -> Action FunctionCategory F
Functor->Action functor = record
  { act      = fmap functor
  ; act-id   = fmap-id functor
  ; act-comp = fmap-comp functor }

Action->Functor : {F : Type u -> Type u}
  -> Action FunctionCategory F -> Functor F
Action->Functor action = record
  { fmap      = act action
  ; fmap-id   = act-id action
  ; fmap-comp = act-comp action }

Action-Functor-roundtrip : {F : Type u -> Type u} -> (act : Action FunctionCategory F) ->
  Functor->Action (Action->Functor act) ≡ act
Action-Functor-roundtrip act = refl

Functor-Action-roundtrip : {F : Type u -> Type u} (functor : Functor F)
  -> Action->Functor (Functor->Action functor) ≡ functor
Functor-Action-roundtrip functor = refl

Functor≃Action : {F : Type u -> Type u}
  -> Functor F ≃ Action FunctionCategory F
Functor≃Action = record
  { to      = Functor->Action
  ; from    = Action->Functor
  ; to-from = Action-Functor-roundtrip
  ; from-to = Functor-Action-roundtrip }
