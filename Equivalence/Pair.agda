{-# OPTIONS --without-K #-}

module Pair where

open import Agda.Primitive                        using (Level; lzero; lsuc; _⊔_)
open import Function                              using (_∘_; id)
open import Relation.Binary.Core                  using (Decidable; REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Equivalence

-- non-dependent sum
record Pair {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B
open Pair public
infixr 4 _,_

swap : {a b : Level} {A : Set a} {B : Set b} → Pair A B → Pair B A
swap (a , b) = (b , a)

sect : {a b : Level} {A : Set a} {B : Set b} → (p : Pair A B) → (swap ∘ swap) p ≡ p
sect _ = refl

retr : {a b : Level} {A : Set a} {B : Set b} → (p : Pair B A) → (swap ∘ swap) p ≡ p
retr _ = refl

adj : {a b : Level} {A : Set a} {B : Set b} → (p : Pair A B) → retr (swap p) ≡ cong swap (sect p)
adj _ = refl

swapIsEquiv : {a b : Level} {A : Set a} {B : Set b} → IsEquiv (Pair A B) (Pair B A) swap
swapIsEquiv = record {f⁻¹ = swap; sect = sect; retr = retr; adj = adj}

swapEquiv : {a b : Level} {A : Set a} {B : Set b} → Pair A B ≃ Pair B A
swapEquiv = record {func = swap; isEquiv = swapIsEquiv}

swap≈ : {a b : Level} {A : Set a} {B : Set b} → REL (Pair A B) (Pair B A) (a ⊔ b)
swap≈ p q = p ≡ (swapEquiv ↑ q)

swapURcoh : {a b : Level} {A : Set a} {B : Set b} → URcoh (Pair A B) (Pair B A) swapEquiv swap≈
swapURcoh =
  record {urCoh = λ _ _ →
    record {func    = id;
            isEquiv = record {f⁻¹  = id;
                              sect = λ _ → refl;
                              retr = λ _ → refl;
                              adj  = λ _ → refl}}}

pairSwap⋈ : {a b : Level} {A : Set a} {B : Set b} → Pair A B ⋈ Pair B A
pairSwap⋈ {A = A} {B = B} = record {equiv = swapEquiv; _≈_ = swap≈; coh = swapURcoh; A= = can= (Pair A B); B= = can= (Pair B A)}
