{-# OPTIONS --without-K #-}

module Leo.EvenOdd where

open import Data.Fin
open import Data.Nat
open import Data.Sum

open import IDesc.IDesc
open import IDesc.Examples.Nat
open import IDesc.Fixpoint
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

data Even : ℕ → Set where
  even0  : Even 0
  evenSS : {n : ℕ} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  odd1  : Odd 1
  oddSS : {n : ℕ} → Odd n → Odd (suc (suc n))

evenOrOddWith : (n : ℕ) → Even n ⊎ Odd n
evenOrOddWith zero       = inj₁ even0
evenOrOddWith (suc zero) = inj₂ odd1
evenOrOddWith (suc (suc n)) with evenOrOddWith n
evenOrOddWith (suc (suc n)) | inj₁ x = inj₁ (evenSS x)
evenOrOddWith (suc (suc n)) | inj₂ y = inj₂ (oddSS y)

evenOrOdd-aux : (n : ℕ) → Even n ⊎ Odd n → Even (suc (suc n)) ⊎ Odd (suc (suc n))
evenOrOdd-aux _ (inj₁ e) = inj₁ (evenSS e)
evenOrOdd-aux _ (inj₂ o) = inj₂ (oddSS o)

evenOrOdd : (n : ℕ) → Even n ⊎ Odd n
evenOrOdd zero          = inj₁ even0
evenOrOdd (suc zero)    = inj₂ odd1
evenOrOdd (suc (suc n)) = evenOrOdd-aux n (evenOrOdd n)

evenOrOdd1 : (n : ℕ) → Even n ⊎ Odd n
evenOrOdd2 : (n : ℕ) → Even (suc n) ⊎ Odd (suc n)

evenOrOdd1 zero    = inj₁ even0
evenOrOdd1 (suc n) = evenOrOdd2 n

evenOrOdd2 zero     = inj₂ odd1
evenOrOdd2 (suc n)  = evenOrOdd-aux n (evenOrOdd1 n)

----

natInd : (P : ℕ → Set) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
natInd P z s zero    = z
natInd P z s (suc n) = s n (natInd P z s n)

SumInd : (A B : Set) → (P : A ⊎ B → Set) → ((a : A) → P (inj₁ a)) → ((b : B) → P (inj₂ b))  → (ab : A ⊎ B) → P ab
SumInd A B P f g (inj₁ ab) = f ab
SumInd A B P f g (inj₂ ab) = g ab

evenOrOddI : (n : ℕ) → Even n ⊎ Odd n
evenOrOddI n =
  natInd
    (λ (n : ℕ) → Even n ⊎ Odd n)
    (inj₁ even0)
    (natInd (λ (n : ℕ) → {!!}) {!!} {!!} {!!})
    n


