{-# OPTIONS --safe --without-K #-}

module CategoryAction.Prelude where

open import Agda.Primitive renaming (Level to Universe; _⊔_ to _uMax_; lsuc to uSuc; Set to Type)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘_; id)

private
  variable
    u w z : Universe
    A B C : Type u

-- Functor from Functional Programming
record Functor (F : Set u -> Set u) : Type (uSuc u) where
  field
    fmap : ∀ {A B : Set u} -> (A -> B) -> F A -> F B

    fmap-id : ∀ {A : Set u} -> (fa : F A) ->
      fmap id fa ≡ fa
    fmap-comp : ∀ {A B C : Type u} (f : A -> B) (g : B -> C) (fa : F A) ->
      fmap (g ∘ f) fa ≡ fmap g (fmap f fa)

-- specialized action for (->)
record Action-> (F : Type u -> Type u) : Type (uSuc u) where
  field
    act : ∀ {A B : Type u} -> (A -> B) -> F A -> F B
    
    act-id : ∀ {A : Type u} (fa : F A) ->
      act id fa ≡ fa
    act-comp : ∀ {A B C : Type u} (f : A -> B) (g : B -> C) (fa : F A) ->
      act (g ∘ f) fa ≡ act g (act f fa)

-- Isomorphism
record _<=>_ (A B : Type u) : Type (uSuc u) where
  field
    to   : A -> B
    from : B -> A
    to-from : ∀ (b : B) -> to (from b) ≡ b
    from-to : ∀ (a : A) -> from (to a) ≡ a

-- Functor ≃ Action of the function category

Functor->Action : {F : Type u -> Type u} -> Functor F -> Action-> F
Functor->Action functor = record
  { act    = fmap functor
  ; act-id = fmap-id functor
  ; act-comp  = fmap-comp functor
  }
  where open Functor

Action->Functor : {F : Type u -> Type u} -> Action-> F -> Functor F
Action->Functor action = record
    { fmap = act action
    ; fmap-id = act-id action
    ; fmap-comp = act-comp action
    }
  where open Action->
 
Functor<=>Action-> : {F : Type u -> Type u} -> Functor F <=> Action-> F
Functor<=>Action-> {u} {F} = record
  { to = Functor->Action
  ; from = Action->Functor
  ; to-from =  \ act -> refl
  ; from-to = \ functor -> refl
  }

-- Action on Op ->

record ActionOp (F : Type u -> Type u) : Type (uSuc u) where
  field
    act : ∀ {A B : Type u} -> (B -> A) -> F A -> F B
    
    act-id : ∀ {A : Type u} (fa : F A) ->
      act id fa ≡ fa
    act-comp : ∀ {A B C : Type u} (f : C -> B) (g : B -> A) (fa : F A) ->
      act (g ∘ f) fa ≡ act f (act g fa)

-- Contravariant from Functional Programming
record Contravariant (F : Set u -> Set u) : Type (uSuc u) where
  field
    contramap : ∀ {A B : Set u} -> (B -> A) -> F A -> F B

    contramap-id : ∀ {A : Set u} -> (fa : F A) ->
      contramap id fa ≡ fa
    contramap-comp : ∀ {A B C : Type u} (f : C -> B) (g : B -> A) (fa : F A) ->
      contramap (g ∘ f) fa ≡ contramap f (contramap g fa)

-- Contravariant <=> Action of the opposite of function category

Contravariant->ActionOp : {F : Type u -> Type u} -> Contravariant F -> ActionOp F
Contravariant->ActionOp contra = record
  { act = contramap contra
  ; act-id =  contramap-id contra
  ; act-comp =  contramap-comp contra
  }
  where open Contravariant

ActionOp->Contravariant : {F : Type u -> Type u} -> ActionOp F -> Contravariant F
ActionOp->Contravariant action = record
  { contramap = act action
  ; contramap-id = act-id action
  ; contramap-comp = act-comp action }
  where open ActionOp
 
Contravariant<=>OAction-> : {F : Type u -> Type u} -> Contravariant F <=> ActionOp F
Contravariant<=>OAction-> {u} {F} = record
  { to = Contravariant->ActionOp
  ; from = ActionOp->Contravariant
  ; to-from =  \ act -> refl
  ; from-to = \ functor -> refl
  }

