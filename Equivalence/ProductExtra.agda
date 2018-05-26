{-# OPTIONS --without-K #-}

module ProductExtra where

open import Agda.Primitive                        using (Level)
open import Data.Product                          using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Product.Properties               using (,-injectiveˡ)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

Σ≡ : {ℓ m : Level} {A : Set ℓ} {B : A → Set m} {a a' : A} {b b' : B a} →
     a ≡ a' → b ≡ b' → (a , b) ≡ (a' , b')
Σ≡ refl refl = refl

,-injective : {ℓ m : Level} {A : Set ℓ} {B : A → Set m} {a a' : A} {b b' : B a} →
     (a , b) ≡ (a' , b') → a ≡ a' × b ≡ b'
,-injective refl = refl , refl

-- replaces the less useful ,-injectiveʳ of the standard library
,-injectiveʳ : {ℓ m : Level} {A : Set ℓ} {B : A → Set m} {ab cd : Σ A B} →
               (e : ab ≡ cd) → subst B (,-injectiveˡ e) (proj₂ ab) ≡ proj₂ cd
,-injectiveʳ refl = refl

