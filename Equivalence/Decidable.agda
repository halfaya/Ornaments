module Decidable where

open import Agda.Primitive                        using (Level)
open import Data.Empty                            using (⊥-elim)
open import Relation.Binary.Core                  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary                      using (yes; no)

open import Equivalence

canonical≟ : {a : Level} {A : Set a} → Decidable {A = A} _≡_ → (x y : A) → x ≡ y → x ≡ y
canonical≟ dec x y e with dec x y
canonical≟ dec x y _ | yes p = p
canonical≟ dec x y e | no ¬p = ⊥-elim (¬p e)

-- TODO: Prove Hedberg's theorem and use for can=refl
can≟ : {a : Level} {A : Set a} → Decidable {A = A} _≡_ → Canonical= A
can≟ dec = record {can= = canonical≟ dec; can=refl = λ _ → {!!}}


