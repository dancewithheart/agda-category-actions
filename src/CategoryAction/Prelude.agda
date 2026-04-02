{-# OPTIONS --safe --without-K #-}

module CategoryAction.Prelude where

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

open Action

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

-- Light equivalence
record _≃_ (A : Type u) (B : Type w) : Type (u uMax w) where
  field
    to   : A -> B
    from : B -> A
    to-from : ∀ (b : B) -> to (from b) ≡ b
    from-to : ∀ (a : A) -> from (to a) ≡ a

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

