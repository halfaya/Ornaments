module Cartesian where

open import Stdlib
open import Signature hiding (_∘_)

record Cartesian {I⁺ I}(Σ⁺ : Sig I⁺)(Σ : Sig I)(u : I⁺ → I) : Set₁ where
  open Sig
  field
    σ   : ∀ i⁺ → Op Σ⁺ i⁺ → Op Σ (u i⁺)
    ρ   : ∀ i⁺ → (op⁺ : Op Σ⁺ i⁺) → Ar Σ (σ i⁺ op⁺) ≡ Ar Σ⁺ op⁺
    coh : ∀ i⁺ op⁺ → (ar : Ar Σ (σ i⁺ op⁺)) → 
          u (Ty Σ⁺ (subst id (ρ i⁺ op⁺) ar)) ≡ Ty Σ ar

⟦_⟧C : ∀{I⁺ I}{Σ⁺ : Sig I⁺}{Σ : Sig I}{u : I⁺ → I} → 
       Cartesian Σ⁺ Σ u → 
       (X : I → Set)(i⁺ : I⁺) → ⟦ Σ⁺ ⟧ (X ∘ u) i⁺ → ⟦ Σ ⟧ X (u i⁺)
⟦ τ ⟧C X i⁺ (op⁺ , args⁺) = σ i⁺ op⁺ , λ ar → 
                                         subst X (coh i⁺ op⁺ ar) 
                                                 (args⁺ (subst id (ρ i⁺ op⁺) ar))
  where open Cartesian τ
