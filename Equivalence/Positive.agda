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
-}

infixl 6 _ℙ+_ _ℕℙ+_

_ℙ+_ : ℙ → ℙ → ℙ
(zero  , ()) ℙ+ (_ , _)
(suc a , _)  ℙ+ (b , _) = suc a + b , s≤s z≤n

-- + for ℕ lifted to ℙ
_ℕℙ+_ : ℙ → ℙ → ℙ
p ℕℙ+ q = ℕ→ℙ (ℙ→ℕ p + ℙ→ℕ q)

-- functional inequivalance
one two : ℙ
one = (1 , s≤s z≤n)
two = (2 , s≤s z≤n)

1+1=2 : one ℙ+ one ≡ two
1+1=2 = refl

1+1=1 : one ℕℙ+ one ≡ one
1+1=1 = refl
