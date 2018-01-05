module Ornament where

open import Stdlib
open import Signature

record COrn {I}(Σ : Sig I)(I⁺ : Set)(u : I⁺ → I) : Set₁ where
  open Sig Σ
  field
    extend : (i⁺ : I⁺) → Op (u i⁺) → Set
    refine : (i⁺ : I⁺)(op : Op (u i⁺))(ext : extend i⁺ op) → Ar op → I⁺
    coh    : (i⁺ : I⁺)(op : Op (u i⁺))(ext : extend i⁺ op)(ar : Ar op) →
                 u (refine i⁺ op ext ar) ≡ Ty ar

⟦_⟧COrn : ∀{I}{Σ : Sig I}{I⁺ u} → COrn Σ I⁺ u → Sig I⁺
⟦_⟧COrn {Σ = Σ}{I⁺}{u} τ  = Op⁺ ◃ Ar⁺ / λ {i⁺}{op⁺} → Ty⁺ {i⁺}{op⁺}
  where open Sig Σ
        open COrn τ

        Op⁺ : I⁺ → Set
        Op⁺ i⁺ = Σ[ op ∈ Op (u i⁺) ] extend i⁺ op

        Ar⁺ : {i⁺ : I⁺} → Op⁺ i⁺ → Set
        Ar⁺ (op , ext) = Ar op
  
        Ty⁺ : {i⁺ : I⁺}{op⁺ : Op⁺ i⁺} → Ar⁺ op⁺ → I⁺
        Ty⁺ {i⁺}{(op , ext)} ar = refine i⁺ op ext ar

