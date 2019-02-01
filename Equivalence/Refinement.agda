{-# OPTIONS --without-K #-}

module Refinement where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.List
open import Data.Nat
open import Data.Product hiding (map)
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

{-
A refinement is just a predicate.
Let's stick to Set₀ for simplicity.
-}
Ref : Set → Set₁
Ref A = Pred A lzero -- (A → Set)

{-
A refinement type is a type plus some refinement.
  RefinementType : (A : Set) → Ref A → Set
  RefinementType A P = Σ A P
Since this is exactly the same as Σ, we just use Σ
to denote a refinement type.
-}

_preserves₁_ : {A : Set} → (A → A) → Ref A → Set
_preserves₁_ {A} f P = (a : A) → P a → P (f a)

_preserves₂_ : {A : Set} → (A → A → A) → Ref A → Set
_preserves₂_ {A} f P = (a b : A) → P a → P b → P (f a b)

lift₁ : {A : Set} → (P : Ref A) → (f : A → A) → f preserves₁ P → (Σ A P → Σ A P)
lift₁ P f p (a , r) = (f a) , (p a r)

lift₂ : {A : Set} → (P : Ref A) → (f : A → A → A) → f preserves₂ P → (Σ A P → Σ A P → Σ A P)
lift₂ P f p (a , r) (b , s) = (f a b) , (p a b r s)

lift₁IsLifting : {A : Set} → (P : Ref A) → (f : A → A) → (p : f preserves₁ P) → 
                 (a : Σ A P) → proj₁ (lift₁ P f p a) ≡ f (proj₁ a)
lift₁IsLifting P f p a = refl

lift₂IsLifting : {A : Set} → (P : Ref A) → (f : A → A → A) → (p : f preserves₂ P) → 
                 (a b : Σ A P) → proj₁ (lift₂ P f p a b) ≡ f (proj₁ a) (proj₁ b)
lift₂IsLifting P f p a b = refl

-- example

Pos : Ref ℕ
Pos = _> 0

ℙ : Set
ℙ = Σ ℕ Pos

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc n)

doublePreservesPos : double preserves₁ Pos
doublePreservesPos zero    ()
doublePreservesPos (suc n) p = s≤s z≤n

doubleℙ : ℙ → ℙ
doubleℙ = lift₁ Pos double doublePreservesPos

+PreservesPos : _+_ preserves₂ Pos
+PreservesPos zero    _ () _
+PreservesPos (suc _) _ _  _ = s≤s z≤n

_+ℙ_ : ℙ → ℙ → ℙ
_+ℙ_ = lift₂ Pos _+_ +PreservesPos

one two three : ℙ
one   = (1 , s≤s z≤n)
two   = (2 , s≤s z≤n)
three = (3 , s≤s z≤n)

1+2=3 : one +ℙ two ≡ three
1+2=3 = refl

{- from Data.List.Base
sum : List ℕ → ℕ
sum = foldr _+_ 0
-}

