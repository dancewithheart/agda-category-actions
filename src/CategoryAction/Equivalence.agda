{-# OPTIONS --safe --without-K #-}

module CategoryAction.Equivalence where

open import Agda.Primitive renaming
  ( Level to Universe
  ; _⊔_   to _uMax_
  ; lsuc  to uSuc
  ; Set   to Type )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘′_; id)

private
  variable
    u w : Universe
    A B : Type u

-- Light equivalence
record _≃_ (A : Type u) (B : Type w) : Type (u uMax w) where
  field
    to   : A -> B
    from : B -> A
    to-from : ∀ (b : B) -> to (from b) ≡ b
    from-to : ∀ (a : A) -> from (to a) ≡ a
