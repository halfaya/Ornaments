module Cartesian.List where

open import Stdlib
open import Signature
open import Signature.List
open import Signature.Nat

open import Cartesian

τList : (A : Set) → Cartesian (ΣList A) ΣNat id
τList A = record { σ = σList 
                 ; ρ = ρList 
                 ; coh = cohList }
      where open Sig

            σList : (tt : ⊤) → Op (ΣList A) tt → Op ΣNat tt
            σList tt (inj₁ tt) = inj₁ tt
            σList tt (inj₂ a) = inj₂ tt

            ρList : (tt : ⊤)(op⁺ : Op (ΣList A) tt) → Ar ΣNat (σList tt op⁺) ≡ Ar (ΣList A) op⁺
            ρList tt (inj₁ tt) = refl
            ρList tt (inj₂ a) = refl

            cohList : (tt : ⊤)(op⁺ : Op (ΣList A) tt)(ar : Ar ΣNat (σList tt op⁺)) →
                        Ty (ΣList A) (subst id (ρList tt op⁺) ar) ≡ Ty ΣNat ar
            cohList tt (inj₁ tt) ()
            cohList tt (inj₂ a) tt = refl
