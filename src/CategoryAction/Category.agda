{-# OPTIONS --safe --without-K #-}

module CategoryAction.Category where

open import Agda.Primitive renaming
  ( Level to Universe
  ; _⊔_   to _uMax_
  ; lsuc  to uSuc
  ; Set   to Type )
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (_∘′_; id)

private
  variable
    u w o m a : Universe
    A B C : Type u

record Category {o m : Universe} : Type (uSuc (o uMax m)) where
  field
    Obj  : Type o
    Hom  : (source : Obj) -> (target : Obj) -> Type m
    cat-id  : ∀ {A : Obj} -> Hom A A
    _comp_  : ∀ {A B C} -> Hom B C -> Hom A B -> Hom A C
    -- laws
    left-id :  ∀ {A B : Obj} -> (f : Hom A B) -> (cat-id comp f) ≡ f
    right-id : ∀ {A B : Obj} -> (f : Hom A B) -> (f comp cat-id) ≡ f
    assoc : ∀ {A B C D : Obj}
      -> (f : Hom A B) -> (g : Hom B C) -> (h : Hom C D)
      -> h comp (g comp f) ≡ (h comp g) comp f

function-comp-left-id : ∀ {A B : Type u} (f : A -> B) -> id ∘′ f ≡ f
function-comp-left-id f = refl

function-comp-right-id : ∀ {A B : Type u} (f : B -> A) -> f ∘′ id ≡ f
function-comp-right-id f = refl

function-comp-assoc : ∀ {A B C D : Type u}
  -> (f : A -> B) -> (g : B -> C) -> (h : C -> D)
  -> h ∘′ g ∘′ f ≡ (h ∘′ g) ∘′ f
function-comp-assoc f g h = refl

function-comp-assoc-inv : ∀ {A B C D : Type u}
  -> (f : B -> A) -> (g : C -> B) (h : D -> C)
  -> (f ∘′ g) ∘′ h ≡ f ∘′ g ∘′ h
function-comp-assoc-inv f g h = refl

FunctionCategory : Category {uSuc u} {u}
FunctionCategory {u} = record
  { Obj      = Type u
  ; Hom      = \ A B -> A -> B
  ; cat-id   = id
  ; _comp_   = _∘′_
  ; left-id  = function-comp-left-id
  ; right-id = function-comp-right-id
  ; assoc    = function-comp-assoc }

OppositeFunctionCategory : Category {uSuc u} {u}
OppositeFunctionCategory {u} = record
  { Obj      = Type u
  ; Hom      = \ A B -> B -> A
  ; cat-id   = id
  ; _comp_   = \ f g -> g ∘′ f
  ; left-id  = function-comp-left-id
  ; right-id = function-comp-right-id
  ; assoc    = function-comp-assoc-inv }
