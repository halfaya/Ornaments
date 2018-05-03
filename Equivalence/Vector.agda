{-# OPTIONS --without-K #-}

module Vector where

open import Agda.Primitive                        using (Level; lzero; lsuc; _⊔_)
open import Data.List                             using (List; length; []; _∷_)
open import Data.Nat                              using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties                   using (suc-injective)
open import Data.Product                          using (Σ; _,_; proj₁; proj₂)
open import Data.Vec                              using (Vec; []; _∷_; _++_)
open import Function                              using (_∘_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Equivalence

LV : {ℓ : Level} → Set ℓ → ℕ → Set ℓ
LV A n = Σ (List A) (λ l → length l ≡ n)

Vec→LV : {ℓ : Level} {A : Set ℓ} → {n : ℕ} → Vec A n → LV A n
Vec→LV []       = [] , refl
Vec→LV (x ∷ xs) = let (ys , p) = Vec→LV xs in x ∷ ys , cong suc p

LV→Vec : {ℓ : Level} {A : Set ℓ} → {n : ℕ} → LV A n → Vec A n
LV→Vec {n = zero}  _            = []
LV→Vec {n = suc n} ([] , ())
LV→Vec {n = suc n} (x ∷ xs , p) = x ∷ LV→Vec (xs , suc-injective p)

VecLVsect : {ℓ : Level} → {A : Set ℓ} → {n : ℕ} → (v : Vec A n) → (LV→Vec ∘ Vec→LV) v ≡ v
VecLVsect []       = refl
VecLVsect (x ∷ xs) = let e = VecLVsect xs in cong (x ∷_) {!!}

VecLVretr : {ℓ : Level} → {A : Set ℓ} → {n : ℕ} → (v : LV A n) → (Vec→LV ∘ LV→Vec ) v ≡ v
VecLVretr {n = zero} ([] , refl)   = refl
VecLVretr {n = zero} (_ ∷ _ , ())
VecLVretr {n = suc n} ([] , ())
VecLVretr {n = suc n} (x ∷ xs , p) = let e = VecLVretr (xs , suc-injective p) in {!!}

VecLVadj : {ℓ : Level} → {A : Set ℓ} → {n : ℕ} → (v : Vec A n) → VecLVretr (Vec→LV v) ≡ cong Vec→LV (VecLVsect v)
VecLVadj []       = refl
VecLVadj (x ∷ xs) = let e = VecLVadj xs in {!!}

VecLVisEquiv : {ℓ : Level} {A : Set ℓ} → {n : ℕ} → IsEquiv (Vec A n) (LV A n) Vec→LV
VecLVisEquiv = record {f⁻¹ = LV→Vec; sect = VecLVsect; retr = VecLVretr; adj = VecLVadj}

instance
  Vec≃LV : {A : Set} → {n : ℕ} → Vec A n ≃ LV A n
  Vec≃LV = record {func = Vec→LV; isEquiv = VecLVisEquiv}

Vec12 : Vec ℕ 2
Vec12 = 1 ∷ 2 ∷ []

Vec345 : Vec ℕ 3
Vec345 = 3 ∷ 4 ∷ 5 ∷ []

LV12 : LV ℕ 2
LV12 = Vec≃LV ↑ Vec12

LV345 : LV ℕ 3
LV345 = Vec≃LV ↑ Vec345

_LV++_ : {ℓ : Level} {m n : ℕ} {A : Set ℓ} → LV A m → LV A n → LV A (m + n)
_LV++_ = {!!}
