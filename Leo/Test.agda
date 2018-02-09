module Test where

data ⊤ : Set where
  tt : ⊤

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

data List (A : Set) : Set where
  []   : List A
  _∷_  : A → List A → List A

extend : ℕ → Set → Set
extend zero    _ = ⊤
extend (suc _) A = A

patch₁ : (n : ℕ) → (A : Set) → extend n A → List A
patch₁ zero    A tt = []
patch₁ (suc _) A a  = a ∷ []

patch₂ : (n : ℕ) → (A : Set) → extend n A → List A
patch₂ zero          A tt = []
patch₂ (suc zero)    A a  = a ∷ patch₂ zero    A tt
patch₂ (suc (suc n)) A a  = a ∷ patch₂ (suc n) A a
