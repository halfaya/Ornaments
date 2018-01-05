module Structure.Composition where

open import Stdlib
open import Signature renaming (_∘_ to _∘C_)
open import Ornament

module Vertical 
       {I⁺⁺ I⁺ I}{Σ : Sig I}{v : I⁺ → I}{v⁺ : I⁺⁺ → I⁺}
       (τ : COrn Σ I⁺ v)(τ⁺ : COrn ⟦ τ ⟧COrn I⁺⁺ v⁺) 
  where

  _∙_ : COrn Σ I⁺⁺ (v ∘ v⁺)
  _∙_ = record { extend = λ i⁺⁺ op → Σ[ ext ∈ extend τ (v⁺ i⁺⁺) op ] extend τ⁺ i⁺⁺ (op , ext) 
               ; refine = λ { i⁺⁺ op (ext , ext⁺) ar → refine τ⁺ i⁺⁺ (op , ext) ext⁺ ar } 
               ; coh = λ { i⁺⁺ op (ext , ext⁺) ar → trans (cong v (coh τ⁺ i⁺⁺ (op , ext) ext⁺ ar)) 
                                                        (coh τ (v⁺ i⁺⁺) op ext ar) } }
    where open COrn


module Horizontal
       {I⁺ I}{Σ₁ : Sig I}{Σ₂ : Sig I}{v : I⁺ → I}
       (τ₁ : COrn Σ₁ I⁺ v)(τ₂ : COrn Σ₂ I⁺ v) 
  where

  _⊚_ : COrn (Σ₂ ∘C Σ₁) I⁺ v
  _⊚_ = record { extend = λ { i⁺ (op₁ , ops₂) → 
                            Σ[ ext₁ ∈ extend τ₁ i⁺ op₁ ] 
                            ((ar₁ : Ar Σ₁ op₁) → 
                                  extend τ₂ (refine τ₁ i⁺ op₁ ext₁ ar₁) 
                                            (subst (Op Σ₂) 
                                                   (sym (coh τ₁ i⁺ op₁ ext₁ ar₁)) 
                                                   (ops₂ ar₁))) }  
               ; refine = λ {i⁺ (op₁ , ops₂) (ext₁ , exts₂) (ar₁ , ar₂) → 
                            refine τ₂ (refine τ₁ i⁺ op₁ ext₁ ar₁) 
                                   (subst (Op Σ₂) (sym (coh τ₁ i⁺ op₁ ext₁ ar₁))
                                          (ops₂ ar₁)) 
                                   (exts₂ ar₁) 
                                   (subst₂ (λ i op₂ → Ar Σ₂ {i} op₂) 
                                            (sym (coh τ₁ i⁺ op₁ ext₁ ar₁)) 
                                            ar₂) }
               ; coh = λ {i⁺ (op₁ , ops₂) (ext₁ , exts₂) (ar₁ , ar₂) →
                       trans (coh τ₂ (refine τ₁ i⁺ op₁ ext₁ ar₁) 
                                   (subst (Op Σ₂) (sym (coh τ₁ i⁺ op₁ ext₁ ar₁))
                                          (ops₂ ar₁)) 
                                   (exts₂ ar₁) 
                                   (subst₂ (λ i op₂ → Ar Σ₂ {i} op₂) 
                                           (sym (coh τ₁ i⁺ op₁ ext₁ ar₁)) 
                                           ar₂)) 
                             (sym (cong₃ (λ i op₂ → Ty Σ₂ {i}{op₂}) 
                                         (sym (coh τ₁ i⁺ op₁ ext₁ ar₁)))) } }
    where open COrn
          open Sig
