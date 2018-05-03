{-# OPTIONS --without-K #-}

module Decidable where

open import Agda.Primitive                        using (Level; lsuc)
open import Data.Empty                            using (⊥-elim)
open import Relation.Binary.Core                  using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary                      using (yes; no)

open import Equivalence

HSet : {a : Level} (A : Set a) → Set a
HSet A = (x y : A) (e e' : x ≡ y) → (e ≡ e')

hedberg : {a : Level} {A : Set a} → Decidable {A = A} _≡_ → HSet A
hedberg dec x .x refl e' with dec x x
hedberg dec x .x refl e' | yes p = {!!}
hedberg dec x .x refl e' | no ¬p = ⊥-elim (¬p e')

canonical≟ : {a : Level} {A : Set a} → Decidable {A = A} _≡_ → (x y : A) → x ≡ y → x ≡ y
canonical≟ dec x y e with dec x y
canonical≟ dec x y _ | yes p = p
canonical≟ dec x y e | no ¬p = ⊥-elim (¬p e)

can≟ : {a : Level} {A : Set a} → Decidable {A = A} _≡_ → Canonical= A
can≟ dec = record {can= = canonical≟ dec; can=refl = λ x → hedberg dec x x (canonical≟ dec x x refl) refl}


