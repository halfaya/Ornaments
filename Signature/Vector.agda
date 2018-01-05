module Signature.Vector where

open import Stdlib
open import Signature

module Model where

  data Vec (A : Set) : ℕ → Set where
    nil : Vec A 0
    cons : ∀ n → (a : A)(xs : Vec A n) → Vec A (suc n)
    

ΣVec : Set → Sig ℕ
ΣVec A = OpVec ◃ (λ {n} → ArVec n) / (λ {n}{op} → TyVec n op)
  where OpVec : ℕ → Set
        OpVec 0 = ⊤
        OpVec (suc n) = A

        ArVec : (n : ℕ) → OpVec n → Set
        ArVec 0 tt = ⊥
        ArVec (suc n) a = ⊤

        TyVec : (n : ℕ)(op : OpVec n) → ArVec n op → ℕ
        TyVec 0 tt ()
        TyVec (suc n) a tt = n

Vec : Set → ℕ → Set
Vec A n = μ (ΣVec A) n

vnil : ∀{A} → Vec A 0
vnil = ⟨ tt , (λ bot → ⊥-elim bot) ⟩

vcons : ∀{A n} → A → Vec A n → Vec A (suc n)
vcons a xs = ⟨ a , (λ { tt → xs }) ⟩
