{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-} -- TODO: remove

module Equivalence where

open import Agda.Primitive                        using (Level; lzero; lsuc; _⊔_)
open import Function                              using (_∘_; id)
open import Relation.Binary.Core                  using (REL)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)

record IsEquiv {a b : Level} (A : Set a) (B : Set b) (f : A → B) : Set (a ⊔ b) where
  field
    f⁻¹  : B → A
    sect : (a : A) → (f⁻¹ ∘ f) a ≡ a
    retr : (b : B) → (f ∘ f⁻¹) b ≡ b
    adj  : (a : A) → retr (f a) ≡ cong f (sect a)
open IsEquiv    

record _≃_ {a b : Level} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  field
    func    : A → B
    isEquiv : IsEquiv A B func
open    _≃_
infix 4 _≃_

_↑_ : {a b : Level} {A : Set a} {B : Set b} → (A ≃ B) → A → B
e ↑ a = func e a

--------

≃sym : {a b : Level} {A : Set a} {B : Set b} → A ≃ B → B ≃ A
≃sym (record {func = f; isEquiv = e}) =
  record {func = f⁻¹ e;
          isEquiv = record {f⁻¹  = f;
                            sect = retr e;
                            retr = sect e;
                            adj  = let x = adj e in {!!}}}

--------

record Canonical= {a : Level} (A : Set a) : Set a where
  field
    can=     : (x y : A) → x ≡ y → x ≡ y
    can=refl : (x : A)   → can= x x refl ≡ refl

-- The canonical canonical equality!
can= : {a : Level} (A : Set a) → Canonical= A
can= A = record {can= = λ _ _ → id; can=refl = λ _ → refl}

record URcoh {a b : Level} (A : Set a) (B : Set b) ( e : A ≃ B ) (_≈_ : REL A B (a ⊔ b)) : Set (a ⊔ b) where
  field
    urCoh : (a a' : A) → (a ≡ a') ≃ (a ≈ (e ↑ a'))

record _⋈_ {a b : Level} (A : Set a) (B : Set b) : Set (lsuc (a ⊔ b)) where
  field
    equiv : A ≃ B
    _≈_   : REL A B (a ⊔ b)
    coh   : URcoh A B equiv _≈_
    A=    : Canonical= A
    B=    : Canonical= B
