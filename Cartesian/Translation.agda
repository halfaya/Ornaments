module Cartesian.Translation where

open import Stdlib
open import Signature
open import Ornament
open import Cartesian
open import Inverse 

module ToOrnament {I⁺ I}{Σ⁺ : Sig I⁺}{Σ : Sig I}{v : I⁺ → I} where

  toOrnament : Cartesian Σ⁺ Σ v → COrn Σ I⁺ v
  toOrnament τ = record { extend = λ i⁺ op → (σ i⁺) ⁻¹ op 
                        ; refine = λ { i⁺ op  (op⁺ , q) ar →
                                       Ty (subst id (ρ i⁺ op⁺) 
                                           (subst (Sig.Ar Σ) (sym q) ar)) } 
                        ; coh = λ { i⁺ .(σ i⁺ op⁺) (op⁺ , refl) ar → 
                                  coh i⁺ op⁺ (subst (Sig.Ar Σ) (sym refl) ar) } }
             where open Cartesian.Cartesian τ
                   open Sig Σ⁺

module ToCartesian {I}{Σ : Sig I}{I⁺}{v : I⁺ → I} where

  toCartesian : (τ : COrn Σ I⁺ v) → Cartesian ⟦ τ ⟧COrn Σ v
  toCartesian τ = record { σ = λ { i⁺ (op , ext) → op }
                         ; ρ = λ { i⁺ (op , ext) → refl } 
                         ; coh = λ { i⁺ (op , ext) ar → coh i⁺ op ext ar } }
              where open COrn τ

