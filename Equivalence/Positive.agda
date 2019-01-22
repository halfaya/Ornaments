{-# OPTIONS --without-K #-}

open import Data.Nat
open import Data.Product
open import Function
open import Relation.Binary.PropositionalEquality

open import Equivalence

{-
Define positive numbers in a standard way.
Note that n > 0 desugars to 1 ≤ n.
-}
n
ℙ : Set
ℙ = Σ ℕ (λ n → n > 0)

{-
Note that Agda's constructors for ≤
are slightly different than Coq's.
-}

ℕ→ℙ : ℕ → ℙ
ℕ→ℙ n = suc n , s≤s z≤n

{-
Construct the rest of the equivalance.
-}

ℙ→ℕ : ℙ → ℕ
ℙ→ℕ (zero  , ())
ℙ→ℕ (suc n , _) = n

ℕ→ℙ→ℕ : (n : ℕ) → (ℙ→ℕ ∘ ℕ→ℙ) n ≡ n
ℕ→ℙ→ℕ n = refl

ℙ→ℕ→ℙ : (p : ℙ) → (ℕ→ℙ ∘ ℙ→ℕ ) p ≡ p
ℙ→ℕ→ℙ (zero  , ())
ℙ→ℕ→ℙ (suc n , s≤s z≤n) = refl

adjℕ→ℙ : (n : ℕ) → ℙ→ℕ→ℙ (ℕ→ℙ n) ≡ cong ℕ→ℙ (ℕ→ℙ→ℕ n)
adjℕ→ℙ n = refl

ℕ≡ℙ : IsEquiv ℕ ℙ ℕ→ℙ
ℕ≡ℙ = record { f⁻¹ = ℙ→ℕ ; sect = ℕ→ℙ→ℕ ; retr = ℙ→ℕ→ℙ ; adj = adjℕ→ℙ }

{-
Addition for positive numbers.
x-}

_ℙ+_ : ℙ → ℙ → ℙ
(zero  , ()) ℙ+ (_ , _)
(suc a , _)  ℙ+ (b , _) = suc a + b , s≤s z≤n

