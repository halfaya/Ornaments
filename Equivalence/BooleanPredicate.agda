{-# OPTIONS --without-K #-}

module BooleanPredicate where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Bool
open import Data.List
open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality
open import Relation.Unary

open import Equivalence

-- boolean predicates
BoolPred : Set → Set
BoolPred A = A → Bool

BoolPredType : (A : Set) → BoolPred A → Set
BoolPredType A P = Σ A ((_≡ true) ∘ P)

-- Nate's example
data ℕ₊ : Bool → Set where
  zero₊ : ℕ₊ false
  suc₊  : {b : Bool} → ℕ₊ b → ℕ₊ true

isPos : {b : Bool} → ℕ₊ b → Bool
isPos {b} n = b

-- induction principle
ℕ₊ind : (P : (b : Bool) → ℕ₊ b → Set) → P false zero₊ → ((b : Bool) → (n : ℕ₊ b) → P b n → P true (suc₊ n)) → (b : Bool) → (n : ℕ₊ b) → P b n
ℕ₊ind P base succ .false zero₊   = base
ℕ₊ind P base succ .true (suc₊ n) = succ (isPos n) n (ℕ₊ind P base succ (isPos n) n)

-- fold for ℕ
fold : {A : Set} → A → (A → A) → ℕ → A
fold base succ zero    = base
fold base succ (suc n) = succ (fold base succ n)

-- positivity is expressible as a fold
-- this is the "indexer"
positive : ℕ → Bool
positive = fold false (λ _ → true)

-- this is easier for proofs
pos : ℕ → Bool
pos zero    = false
pos (suc n) = true

-- "packed Σ" ℕ indexed by Bool
ℕ′ : Set
ℕ′ = Σ Bool ℕ₊

ℙ : Set
ℙ = ℕ₊ true

ℕ→ℕ₊ : (n : ℕ) → ℕ₊ (pos n)
ℕ→ℕ₊ zero    = zero₊
ℕ→ℕ₊ (suc n) = suc₊ (ℕ→ℕ₊ n)

ℕ₊→ℕ : {b : Bool} → ℕ₊ b → ℕ
ℕ₊→ℕ zero₊    = zero
ℕ₊→ℕ (suc₊ n) = suc (ℕ₊→ℕ n)

ℕ₊→ℕind : (b : Bool) → ℕ₊ b → ℕ
ℕ₊→ℕind = ℕ₊ind (λ _ _ → ℕ) zero (λ _ _ m → suc m) 

ℕ→ℕ₊→ℕ : (n : ℕ) → (ℕ₊→ℕ ∘ ℕ→ℕ₊) n ≡ n
ℕ→ℕ₊→ℕ zero    = refl
ℕ→ℕ₊→ℕ (suc n) = cong suc (ℕ→ℕ₊→ℕ n) 

{-
These can't be stated without a subst on types, which in
turn will complicate the proof.

ℕ₊→ℕ→ℕ₊ : {b : Bool} → (n : ℕ₊ b) → (ℕ→ℕ₊ ∘ ℕ₊→ℕ) n ≡ n
ℕ₊→ℕ→ℕ₊ n = ?

ℕ₊→ℕ→ℕ₊ind : (b : Bool) → (n : ℕ₊ b) → (ℕ→ℕ₊ ∘ ℕ₊→ℕind b) n ≡ n
ℕ₊→ℕ→ℕ₊ind n = ?
-} 

ℕ→ℕ′ : ℕ → ℕ′
ℕ→ℕ′ n = pos n , ℕ→ℕ₊ n

ℕ′→ℕ : ℕ′ → ℕ
ℕ′→ℕ (_ , n) = ℕ₊→ℕ n

ℕ→ℕ′→ℕ : (n : ℕ) → (ℕ′→ℕ ∘ ℕ→ℕ′) n ≡ n
ℕ→ℕ′→ℕ zero    = refl
ℕ→ℕ′→ℕ (suc n) = cong suc (ℕ→ℕ′→ℕ n)

{-
Requires ℕ₊→ℕ→ℕ₊

ℕ′→ℕ→ℕ′ : (n : ℕ′) → (ℕ→ℕ′ ∘ ℕ′→ℕ) n ≡ n
ℕ′→ℕ→ℕ′ (.false , zero₊) = refl
ℕ′→ℕ→ℕ′ (.true , suc₊ n) = cong₂ _,_ refl (cong suc₊ (ℕ₊→ℕ→ℕ₊ n))

adjℕ→ℕ′ : (n : ℕ) → ℕ′→ℕ→ℕ′ (ℕ→ℕ′ n) ≡ cong ℕ→ℕ′ (ℕ→ℕ′→ℕ n)
adjℕ→ℕ′ n = ?

ℕ≡ℕ′ : IsEquiv ℕ ℕ′ ℕ→ℕ′
ℕ≡ℕ′ = record { f⁻¹ = ℕ′→ℕ ; sect = ℕ→ℕ′→ℕ ; retr = ℕ′→ℕ→ℕ′ ; adj = adjℕ→ℕ′ }
-}

{-
We can now lift functions.
Let's be perverse and just lift the output.
-}

_+′_ : ℕ → ℕ → ℕ′
m +′ n = ℕ→ℕ′(m + n)

_+ℙ_ : ℕ → ℕ → ℙ
m +ℙ n = {!!}
