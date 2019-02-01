{-# OPTIONS --without-K #-}

module Positive where

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

ℙ→ℕ→ℙ : (p : ℙ) → (ℕ→ℙ ∘ ℙ→ℕ) p ≡ p
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

-- double

double : ℕ → ℕ
double zero    = zero
double (suc n) = suc (suc (double n))

double' : ℕ → ℕ
double' n = double (suc n)

ℕℙdouble : ℙ → ℙ
ℕℙdouble p = ℕ→ℙ (double (ℙ→ℕ p))

ℕℙdouble' : ℙ → ℙ
ℕℙdouble' p = ℕ→ℙ (double' (ℙ→ℕ p))

x = ℕℙdouble' two

-- Injection

{-
With injection, we map ℙ to ℕ directly
((n , _) → n) but we also want to keep
the proof of positivity which is best
stored in a product type, so with this
representation of ℙ the map is the
identity function, which is trivially
an equivalance.
-}

P→N : ℙ → Σ ℕ (λ n → n > 0)
P→N p = p

N→P : Σ ℕ (λ n → n > 0) → ℙ
N→P p = p

P→N→P : (p : ℙ) → (N→P ∘ P→N) p ≡ p
P→N→P _ = refl

N→P→N : (n : Σ ℕ (λ n → n > 0)) → (P→N ∘ N→P) n ≡ n
N→P→N _ = refl

adjP→N : (p : ℙ) → N→P→N (P→N p) ≡ cong P→N (P→N→P p)
adjP→N _ = refl

P≡N : IsEquiv ℙ (Σ ℕ (λ n → n > 0)) P→N
N≡P = record { f⁻¹ = N→P ; sect = P→N→P ; retr = N→P→N  ; adj = adjP→N }

{-
What's more interesting is lifting.
Plus can be lifted in 8 ways but assume we want the ℙ → ℙ → ℙ version.
We transform the inputs to ℕ but keep the proofs.
Then using the input ℕs and proofs we need to provide a proof that
the output is positive. The hard part would be to automate proving
the lemma below.
-}

lemma : (m n : Σ ℕ (λ n → n > 0)) → (proj₁ m + proj₁ n > 0)
lemma (zero  , ()) _
lemma (suc _ , _ ) _ = s≤s z≤n

_P+_ : ℙ → ℙ → ℙ
p P+ q = N→P (proj₁ (P→N p) + proj₁ (P→N q) , lemma (P→N p) (P→N q))

