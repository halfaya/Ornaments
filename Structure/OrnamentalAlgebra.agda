open import Stdlib

open import Signature hiding (_∘_)
open import Cartesian

module Structure.OrnamentalAlgebra 
       {I⁺ I}{Σ⁺ : Sig I⁺}{Σ : Sig I}{v : I⁺ → I}
       (τ : Cartesian Σ⁺ Σ v)
  where

forget : ∀{i⁺} → ⟦ Σ⁺ ⟧ (μ Σ ∘ v) i⁺ → μ Σ (v i⁺)
forget {i⁺} xs = ⟨ ⟦ τ ⟧C (μ Σ ) i⁺ xs ⟩
