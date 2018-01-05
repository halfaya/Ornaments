module Ornament.List where

open import Stdlib
open import Ornament
open import Signature
open import Signature.Nat

τList : Set → COrn ΣNat ⊤ id
τList A = record { extend = extendList 
                 ; refine = refineList 
                 ; coh = cohList }
      where open Sig ΣNat

            extendList : (tt : ⊤) → Op tt → Set
            extendList tt (inj₁ tt) = ⊤
            extendList tt (inj₂ tt) = A

            refineList : (tt : ⊤)(op : Op tt) → extendList tt op → Ar op → ⊤
            refineList _ _ _ _ = tt

            cohList : (tt : ⊤)(op : Op tt)(ext : extendList tt op)
                (ar : Ar op) → tt ≡ Ty ar
            cohList tt op ext arr = refl
