{-# OPTIONS --without-K #-}

module Leo.Pos2 where

open import Data.Bool
open import Data.Nat
open import Data.Product

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

-- this should be equivalent to the above two
ZeroPosΣ : Set
ZeroPosΣ = Σ Bool (λ b → Σ ℕ (λ n → isPos n ≡ b))

