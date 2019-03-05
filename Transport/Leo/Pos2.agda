{-# OPTIONS --without-K #-}

module Transport.Leo.Pos2 where

open import Data.Bool
open import Data.Nat
open import Data.Product

open import Equivalence.Equivalence

open import Function

open import Relation.Binary.PropositionalEquality

data ZeroPos : Bool → Set where
  zero : ZeroPos false
  suc  : {b : Bool} → (n : ZeroPos b) → ZeroPos true

-- another possibility
data ZeroPos1 : Bool → Set where
  zero : ZeroPos1 false
  one  : ZeroPos1 true
  suc  : (n : ZeroPos1 true) → ZeroPos1 true

isPos : ℕ → Bool
isPos zero    = false
isPos (suc n) = true

-- the following two should be equivalent
ZeroPosΣ : Set
ZeroPosΣ = Σ Bool (λ b → ZeroPos b)

ZeroPosΣ′ : Set
ZeroPosΣ′ = Σ Bool (λ b → Σ ℕ (λ n → isPos n ≡ b))

-- Equivalence between ZeroPos and ℕ

ZP→N : ZeroPosΣ → ℕ
ZP→N (false , zero)        = zero
ZP→N (true  , suc zero)    = suc zero
ZP→N (true  , suc (suc n)) = suc (ZP→N (true , suc n))

N→ZP : ℕ → ZeroPosΣ
N→ZP zero    = false , zero
N→ZP (suc n) = true  , suc (proj₂ (N→ZP n))

ZP→N→ZP : (p : ZeroPosΣ) → (N→ZP ∘ ZP→N) p ≡ p
ZP→N→ZP (false , zero)  = refl
ZP→N→ZP (true , suc zero) = refl
ZP→N→ZP (true , suc (suc n)) = let x = ZP→N→ZP (true , suc n) in {!!}

N→ZP→N : (n : ℕ) → (ZP→N ∘ N→ZP) n ≡ n
N→ZP→N zero          = refl
N→ZP→N (suc zero)    = refl
N→ZP→N (suc (suc n)) = let x = N→ZP→N n in {!!}

adjZP→N : (p : ZeroPosΣ) → N→ZP→N (ZP→N p) ≡ cong ZP→N (ZP→N→ZP p)
adjZP→N p = {!!}

ZP≡N : IsEquiv ZeroPosΣ ℕ ZP→N
ZP≡N = record { f⁻¹ = N→ZP ; sect = ZP→N→ZP ; retr = N→ZP→N  ; adj = adjZP→N }

_ZP+_ : ZeroPosΣ → ZeroPosΣ → ZeroPosΣ
m ZP+ n = N→ZP (ZP→N m + ZP→N n)

zp1 zp2 zp3 : ZeroPosΣ
zp1 = true , suc zero
zp2 = true , suc (suc zero)
zp3 = true , suc (suc (suc zero))

1+2=3 : zp1 ZP+ zp2 ≡ zp3
1+2=3 = refl
