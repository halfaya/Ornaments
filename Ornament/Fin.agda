module Ornament.Fin where

open import Stdlib
open import Ornament
open import Signature
open import Signature.Nat

τFin : COrn ΣNat ℕ (λ n → tt)
τFin = record { extend = extendFin 
              ; refine = refineFin
              ; coh = cohFin }
      where open Sig ΣNat

            extendFin : (n : ℕ) → Op tt → Set
            extendFin n _ = ∃ λ n' → n ≡ suc n'

            refineFin : (n : ℕ)(op : Op tt) → extendFin n op → Ar op → ℕ
            refineFin .(suc n) (inj₁ tt) (n , refl) ()
            refineFin .(suc n) (inj₂ tt) (n , refl) tt = n

            cohFin : (n : ℕ)(op : Op tt)(ext : extendFin n op)(ar : Ar op) → 
                tt ≡ Ty ar
            cohFin n op ext arr = refl
