module Inverse where

open import Stdlib

_⁻¹_ : {A B : Set}(f : A → B) → B → Set
f ⁻¹ b = Σ[ a ∈ _ ] f a ≡ b
