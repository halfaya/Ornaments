module Signature.List where

open import Stdlib
open import Signature

module Model where

  data List (A : Set) : Set where
    nil : List A
    cons : (a : A)(xs : List A) → List A

ΣList : Set → Sig ⊤
ΣList A = OpList ◃ ArList / TyList
  where OpList : ⊤ → Set
        OpList tt = ⊤ ⊎ A

        ArList : {tt : ⊤} → OpList tt → Set
        ArList (inj₁ tt) = ⊥
        ArList (inj₂ a) = ⊤

        TyList : {tt : ⊤}{op : OpList tt} → ArList op → ⊤
        TyList _ = tt

List : Set → Set
List A = μ (ΣList A) tt

nil : ∀{A} → List A
nil = ⟨ inj₁ tt , (λ bot → ⊥-elim bot) ⟩

cons : ∀{A} → A → List A → List A
cons a xs = ⟨ inj₂ a , (λ { tt → xs }) ⟩

