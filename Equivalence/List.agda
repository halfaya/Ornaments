{-# OPTIONS --without-K #-}

module List where

open import Agda.Primitive                        using (Level; lzero; lsuc; _⊔_)
open import Data.List                             using (List; length; []; _∷_)
open import Data.List.Properties                  using (++-identityʳ)
open import Data.Nat                              using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties                   using (suc-injective)
open import Data.Product                          using (Σ; _,_; proj₁; proj₂; _×_)
open import Data.Product.Properties               using (,-injectiveˡ)
open import Data.Vec                              using (Vec; []; _∷_; _++_)
open import Function                              using (_∘_)
open import Relation.Binary.Core                  using (Decidable; REL)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Relation.Nullary                      using (yes; no; ¬_)

open import Equivalence

-- equivalence of a list with a "sigma vector"

ΣV : {ℓ : Level} → Set ℓ → Set ℓ
ΣV A = Σ ℕ (λ n → Vec A n)

L→ΣV : {ℓ : Level} {A : Set ℓ} → List A → ΣV A
L→ΣV []       = 0 , []
L→ΣV (x ∷ xs) = let (n , v) = L→ΣV xs in suc n , x ∷ v

ΣV→L : {ℓ : Level} {A : Set ℓ} → ΣV A → List A
ΣV→L (zero  , [])    = []
ΣV→L (suc n , x ∷ v) = x ∷ ΣV→L (n , v)

LΣVsect : {ℓ : Level} → {A : Set ℓ} → (l : List A) → (ΣV→L ∘ L→ΣV) l ≡ l
LΣVsect []                          = refl
LΣVsect (x ∷ xs) rewrite LΣVsect xs = refl

LΣVretr : {ℓ : Level} → {A : Set ℓ} → (v : ΣV A) → (L→ΣV ∘ ΣV→L) v ≡ v
LΣVretr (zero  , [])                            = refl
LΣVretr (suc n , x ∷ v) rewrite LΣVretr (n , v) = refl

LΣVadj : {ℓ : Level} {A : Set ℓ} → (l : List A) → LΣVretr (L→ΣV l) ≡ cong L→ΣV (LΣVsect l)
LΣVadj []                                      = refl
LΣVadj (x ∷ xs) rewrite LΣVadj xs | LΣVsect xs = refl

L→ΣVIsEquiv : {ℓ : Level} {A : Set ℓ}  → IsEquiv (List A) (ΣV A) L→ΣV
L→ΣVIsEquiv = record {f⁻¹ = ΣV→L; sect = LΣVsect; retr = LΣVretr; adj = LΣVadj}

L→ΣVEquiv : {ℓ : Level} {A : Set ℓ}  → List A ≃ ΣV A
L→ΣVEquiv = record {func = L→ΣV; isEquiv = L→ΣVIsEquiv}

L→ΣV≈ : {ℓ : Level} {A : Set ℓ} → REL (List A) (ΣV A) ℓ
L→ΣV≈ l v = L→ΣVEquiv ↑ l ≡ v

-- note that ++-identityʳ is Agda's version of Coq's app_nil_r

