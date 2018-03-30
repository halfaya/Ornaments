module Equivalence where

open import Data.Empty                            using (⊥-elim)
open import Relation.Binary.Core                  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary                      using (yes; no)

canonical≟ : ∀ {ℓ} {A : Set ℓ} → Decidable {A = A} _≡_ → (x y : A) → x ≡ y → x ≡ y
canonical≟ hdec x y e with hdec x y
canonical≟ hdec x y _ | yes p = p
canonical≟ hdec x y e | no ¬p = ⊥-elim (¬p e)
