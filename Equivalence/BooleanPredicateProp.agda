{-# OPTIONS --without-K --prop #-}

module BooleanPredicateProp where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Bool
open import Data.List
open import Data.Nat
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

data ⊥ : Prop where

record ⊤ : Prop where
  constructor tt

data Bad : Prop where
  zero : Bad
  one  : Bad

data Squash {ℓ : Level} (A : Set ℓ) : Prop ℓ where
  squash : A → Squash A

squash-elim : ∀ {ℓ₁ ℓ₂ : Level} (A : Set ℓ₁) (P : Prop ℓ₂) → (A → P) → Squash A → P
squash-elim A P f (squash x) = f x

Bool→Bad : Bool → Bad
Bool→Bad false = zero
Bool→Bad true  = one

Bool→Prop : Bool → Prop
Bool→Prop false = ⊥
Bool→Prop true  = ⊤

Prop→Bool : Prop → Bool
Prop→Bool _ = true

x = Prop→Bool ⊥

record Σ {a : Level} (A : Set a) (B : A → Prop) : Set a where
  constructor _,_
  field
    fst : A
    snd : B fst
open Σ public
infixr 4 _,_

-- refinements into Prop rather than Set
Ref : Set → Set₁
Ref A = A → Prop

RefType : (A : Set) → Ref A → Set
RefType A P = Σ A P

-- boolean predicates
BoolPred : Set → Set
BoolPred A = A → Bool

BoolPredType : (A : Set) → BoolPred A → Set
BoolPredType A P = Σ A (Bool→Prop ∘ P)

BoolPred→Ref : (A : Set) → BoolPred A → Ref A
BoolPred→Ref A f = Bool→Prop ∘ f

Ref→BoolPred : (A : Set) → Ref A → BoolPred A
Ref→BoolPred A f = {!!}


