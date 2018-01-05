module Signature.Tree where

open import Stdlib
open import Signature

module Model where

  data Tree (A : Set) : Set where
    leaf : Tree A
    node : (a : A)(lb : Tree A)(rb : Tree A) → Tree A

ΣTree : Set → Sig ⊤
ΣTree A = OpTree ◃ ArTree / TyTree
  where OpTree : ⊤ → Set
        OpTree tt = ⊤ ⊎ A

        ArTree : {tt : ⊤} → OpTree tt → Set
        ArTree (inj₁ tt) = ⊥
        ArTree (inj₂ a) = ⊤ ⊎ ⊤

        TyTree : {tt : ⊤}{op : OpTree tt} → ArTree op → ⊤
        TyTree _ = tt

Tree : Set → Set
Tree A = μ (ΣTree A) tt

leaf : ∀{A} → Tree A
leaf = ⟨ inj₁ tt , (λ bot → ⊥-elim bot) ⟩

node : ∀{A} → A → Tree A → Tree A → Tree A
node a l r = ⟨ inj₂ a , (λ { (inj₁ tt) → l 
                           ; (inj₂ tt) → r }) ⟩

