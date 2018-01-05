module Signature.Nat where

open import Stdlib
open import Signature

module Model where

  data Nat : Set where
    ze : Nat
    suc : (n : Nat) → Nat

ΣNat : Sig ⊤
ΣNat = OpNat ◃ ArNat / TyNat
  where OpNat : ⊤ → Set
        OpNat tt = ⊤ ⊎ ⊤

        ArNat : {tt : ⊤} → OpNat tt → Set
        ArNat (inj₁ tt) = ⊥
        ArNat (inj₂ tt) = ⊤

        TyNat : {tt : ⊤}{op : OpNat tt} → ArNat op → ⊤
        TyNat _ = tt

Nat : Set
Nat = μ ΣNat tt

ze : Nat
ze = ⟨ inj₁ tt , (λ bot → ⊥-elim bot) ⟩

su : Nat → Nat
su n = ⟨ inj₂ tt , (λ { tt → n }) ⟩

