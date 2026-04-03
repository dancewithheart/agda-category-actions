{-# OPTIONS --safe --without-K #-}

module CategoryAction.KleisliAction where

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

record Monad (F : Type u -> Type u) : Type (uSuc u) where
  field
    pure : {A : Type u} -> A -> F A
    join : {A B : Type u} -> (B -> F C) -> (A -> F B) -> A -> F C
    -- laws
    -- TODO

open Monad

KleisliCategory : (F : Type u -> Type u) -> Monad F -> Category {uSuc u} {u}
KleisliCategory {u} F b = record
  { Obj      = Type u
  ; Hom      = \ A B -> A -> F B
  ; cat-id   = pure b
  ; _comp_   = join b
  ; left-id  = {!!}
  ; right-id = {!!}
  ; assoc    = {!!} }

open Action

-- Monad ≃ Action of the Kleisli category

Monad->Action : {F : Type u -> Type u} -> Monad F -> Action KleisliCategory F
Monad->Action bind = record
  { act      = {!!}
  ; act-id   = {!!}
  ; act-comp = {!!} }

{--
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
--}

{-- Kleisli action presentation.

record BindAction (F : Type u → Type u) : Type (lsuc u) where
  field
    act : {A B : Type u} → (A → F B) → F A → F B

    act-id :
      {A : Type u} →
      (fa : F A) →
      act (λ a → a pure?) fa ≡ fa

    act-∘ :
      {A B C : Type u} →
      (f : A → F B) →
      (g : B → F C) →
      (fa : F A) →
      act (λ a → act g (f a)) fa ≡ act g (act f fa)
-}
