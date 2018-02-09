module Leo.SizedTree where

open import Stdlib
open import Signature
open import Leo.Nat

module Model where

  data SizedTree (A : Set) : ℕ → Set where
    leaf : SizedTree A zero
    node : {m n : ℕ}(a : A)(lb : SizedTree A m)(rb : SizedTree A n) → SizedTree A (suc (m + n))

ΣSizedTree : Set → Sig ℕ
ΣSizedTree A = OpSizedTree ◃ (λ {n} → ArSizedTree n) / (λ {n}{op} → TySizedTree n op)
  where OpSizedTree : ℕ → Set
        OpSizedTree zero    = ⊤
        OpSizedTree (suc n) = A

        ArSizedTree : (n : ℕ) → OpSizedTree n → Set
        ArSizedTree zero    tt = ⊥
        ArSizedTree (suc _) _  = ⊤ ⊎ ⊤

        TySizedTree : (n : ℕ)(op : OpSizedTree n) → ArSizedTree n op → ℕ
        TySizedTree zero tt ()
        TySizedTree (suc n) op (inj₁ tt) = n
        TySizedTree (suc n) op (inj₂ tt) = n

{-
SizedTree : Set → Set
SizedTree A = μ (ΣSizedTree A) tt

leaf : ∀{A} → SizedTree A
leaf = ⟨ inj₁ tt , (λ bot → ⊥-elim bot) ⟩

node : ∀{A} → A → SizedTree A → SizedTree A → SizedTree A
node a l r = ⟨ inj₂ a , (λ { (inj₁ tt) → l 
                           ; (inj₂ tt) → r }) ⟩
-}
