module Signature.Fin where

open import Stdlib
open import Signature

module Model where

  data Fin : ℕ → Set where
    fz : ∀ n → Fin (suc n)
    fs : ∀ n → Fin n → Fin (suc n)

ΣFin : Sig ℕ
ΣFin = OpFin ◃ (λ {n} → ArFin n) / (λ {n}{op} → TyFin n op)
  where OpFin : ℕ → Set
        OpFin 0 = ⊥
        OpFin (suc n) = ⊤ ⊎ ⊤

        ArFin : (n : ℕ) → OpFin n → Set
        ArFin 0 ()
        ArFin (suc n) (inj₁ tt) = ⊥
        ArFin (suc n) (inj₂ tt) = ⊤

        TyFin : (n : ℕ)(op : OpFin n) → ArFin n op → ℕ
        TyFin 0 ()
        TyFin (suc n) _ _ = n

Fin : ℕ → Set
Fin n = μ ΣFin n

fze : ∀{n} → Fin (suc n)
fze = ⟨ inj₁ tt , (λ bot → ⊥-elim bot) ⟩

fsu : ∀{n} → Fin n → Fin (suc n)
fsu k = ⟨ inj₂ tt , (λ { tt → k }) ⟩

