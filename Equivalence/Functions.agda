{-# OPTIONS --without-K #-}
{-# OPTIONS --allow-unsolved-metas #-} -- TODO: remove

module Functions where

open import Agda.Primitive                        using (Level; lzero; lsuc; _⊔_)
open import Function                              using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)


open import Equivalence
open        IsEquiv
open        _≃_

fTransport : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → A ≃ B → (A → C) → (B → C)
fTransport e f = f ∘ f⁻¹ (isEquiv e)

fEq : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → (f : A → C) → (e : A ≃ B) → (a : A) → fTransport e f (e ↑ a) ≡ f a
fEq f e a = cong f (sect (isEquiv e) a)

f≃ : {a b c : Level} {A : Set a} {B : Set b} {C : Set c} → A ≃ B → (A → C) ≃ (B → C)
f≃ e = record {func    = fTransport e;
               isEquiv = record {f⁻¹  = fTransport (≃sym e);
                                 sect = {!!};
                                 retr = {!!};
                                 adj  = {!!}}}

