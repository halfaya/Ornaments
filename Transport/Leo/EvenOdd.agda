{-# OPTIONS --without-K #-}

module Leo.EvenOdd where

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_)
open import Data.Fin
open import Data.Nat
open import Data.Product
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

-- original, naturdal definition in Agda
evenOrOddWith : (n : ℕ) → Even n ⊎ Odd n
evenOrOddWith zero       = inj₁ even0
evenOrOddWith (suc zero) = inj₂ odd1
evenOrOddWith (suc (suc n)) with evenOrOddWith n
evenOrOddWith (suc (suc n)) | inj₁ x = inj₁ (evenSS x)
evenOrOddWith (suc (suc n)) | inj₂ y = inj₂ (oddSS y)

-- To desugar with, construct an aux function.
evenOrOdd-aux : (n : ℕ) → Even n ⊎ Odd n → Even (suc (suc n)) ⊎ Odd (suc (suc n))
evenOrOdd-aux _ (inj₁ e) = inj₁ (evenSS e)
evenOrOdd-aux _ (inj₂ o) = inj₂ (oddSS o)

-- If we don't want to split twice on n, we can use mutually recursive functions.
evenOrOdd1 : (n : ℕ) → Even n ⊎ Odd n
evenOrOdd2 : (n : ℕ) → Even (suc n) ⊎ Odd (suc n)

evenOrOdd1 zero    = inj₁ even0
evenOrOdd1 (suc n) = evenOrOdd2 n

evenOrOdd2 zero    = inj₂ odd1
evenOrOdd2 (suc n) = evenOrOdd-aux n (evenOrOdd1 n)

-- The original evenOrOddWith, desugared.
-- We will convert this into pure eliminators.
evenOrOdd : (n : ℕ) → Even n ⊎ Odd n
evenOrOdd zero          = inj₁ even0
evenOrOdd (suc zero)    = inj₂ odd1
evenOrOdd (suc (suc n)) = evenOrOdd-aux n (evenOrOdd n)

-------------------

-- induction principles

natInd : {ℓ : Level}(P : ℕ → Set ℓ) → P zero → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
natInd P z s zero    = z
natInd P z s (suc n) = s n (natInd P z s n)

-- "2-inducton" for ℕ
natInd2 : (P : ℕ → Set) → P zero → P (suc zero) → ((n : ℕ) → P n → P (suc n) → P (suc (suc n))) → (n : ℕ) → P n
natInd2 P z o s zero          = z
natInd2 P z o s (suc zero)    = o
natInd2 P z o s (suc (suc n)) = s n (natInd2 P z o s n) (natInd2 P z o s (suc n))

sumInd : (A B : Set) → (P : A ⊎ B → Set) → ((a : A) → P (inj₁ a)) → ((b : B) → P (inj₂ b))  → (ab : A ⊎ B) → P ab
sumInd A B P f g (inj₁ ab) = f ab
sumInd A B P f g (inj₂ ab) = g ab

-- evenOrOdd-aux defined with sumInd
evenOrOdd-auxI : (n : ℕ) → Even n ⊎ Odd n → Even (suc (suc n)) ⊎ Odd (suc (suc n))
evenOrOdd-auxI n =
  sumInd
    (Even n)
    (Odd n)
    (λ _ → Even (suc (suc n)) ⊎ Odd (suc (suc n)))
    (λ a → inj₁ (evenSS a))
    (λ b → inj₂ (oddSS b))

-- evenOrOdd defined with natInd2
evenOrOddI2 : (n : ℕ) → Even n ⊎ Odd n
evenOrOddI2 =
  natInd2
    (λ n → Even n ⊎ Odd n)
    (inj₁ even0)
    (inj₂ odd1)
    λ n h _ → evenOrOdd-auxI n h

-----------------

-- Belowℕ and recℕ are used to encode complete induction in type theory.
-- They can be defined in terms of ordinary natInd.

Belowℕ : (P : ℕ → Set) → ℕ → Set
Belowℕ P =
  natInd
    (λ _ → Set)
    ⊤
    λ n h → h × P n
--Belowℕ P zero    = ⊤
--Belowℕ P (suc n) = Belowℕ P n × P n

belowℕ : (P : ℕ → Set) (p : (n : ℕ) → Belowℕ P n → P n) (n : ℕ) → Belowℕ P n
belowℕ P p =
  natInd
    (λ n → Belowℕ P n)
    tt
    λ n h → h , p n h
--belowℕ P p zero    = tt
--belowℕ P p (suc n) = let b = belowℕ P p n in b , p n b

-- complete induction on ℕ
recℕ : (P : ℕ → Set) (p : (n : ℕ) → Belowℕ P n → P n) (n : ℕ) → P n
recℕ P p n = p n (belowℕ P p n)

-- Now define 2-induction as a special case of complete induction.
-- Note that as Below handles all the recursive calls, the calls
-- to natInd never use the induction hypothesis and could be replaced by "case".
natInd2I : (P : ℕ → Set) → P zero → P (suc zero) → ((n : ℕ) → P n → P (suc n) → P (suc (suc n))) → (n : ℕ) → P n
natInd2I P z o s = recℕ P p
  where p :  (n : ℕ) → Belowℕ P n → P n
        q :  (n : ℕ) → Belowℕ P (suc n) → P (suc n)
        p = natInd
              (λ n → Belowℕ P n → P n)
              (λ _ → z)
              λ n _ b →  q n b
--        p zero    _ = z
--        p (suc n) b = q n b
        q = natInd
              (λ n → Belowℕ P (suc n) → P (suc n))
              (λ _ → o)
              λ n _ b → s n (proj₂ (proj₁ b)) (proj₂ b)
--        q zero    b = o
--        q (suc n) b = s n (proj₂ (proj₁ b)) (proj₂ b)

-- evenOrOdd defined purely with natInd
evenOrOddI : (n : ℕ) → Even n ⊎ Odd n
evenOrOddI =
  natInd2I
    (λ n → Even n ⊎ Odd n)
    (inj₁ even0)
    (inj₂ odd1)
    λ n h _ → evenOrOdd-auxI n h
