{-# OPTIONS --safe --without-K #-}

module CategoryAction.Action where

open import Agda.Primitive renaming
  ( Level to Universe
  ; _⊔_   to _uMax_
  ; lsuc  to uSuc
  ; Set   to Type )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘′_; id)

open import CategoryAction.Category
open import CategoryAction.Equivalence

private
  variable
    u w o m a : Universe
    A B C : Type u

record Action {o m a : Universe} (C : Category {o} {m})
    (F : Category.Obj C -> Type a) : Type (o uMax m uMax a) where
  open Category C
  field
    act : ∀ {A B} -> Hom A B -> F A -> F B
    -- laws
    act-id : ∀ {A} (fa : F A) ->
      act cat-id fa ≡ fa

    act-comp : ∀ {A B C} (f : Hom A B) (g : Hom B C) (fa : F A) ->
      act (g comp f) fa ≡ act g (act f fa)

