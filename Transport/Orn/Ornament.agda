{-# OPTIONS --without-K #-}

module Orn.Ornament where

open import Function

open import Data.Nat hiding (_⊔_)
open import Data.Fin

open import Logic.Logic

open import IDesc.IDesc


-- Paper: Definition 4.1
data Orn {I K : Set}(u : I → K) : IDesc K → Set₁ where
  -- Insert
  insert : ∀{D} → (S : Set )(D⁺ : S → Orn u D) → Orn u D

  -- Refine
  `var : {k : K} → (k⁻¹ : u ⁻¹ k) → Orn u (`var k)
  
  -- Copy
  `1 : Orn u `1
  _`×_ : ∀{D D'} → (D⁺ : Orn u D)(D'⁺ : Orn u D') → Orn u (D `× D')
  `σ : {n : ℕ}{T : Fin n → IDesc K} → (T⁺ : (k : Fin n) → Orn u (T k)) → Orn u (`σ n T)
  `Σ : ∀{S T} → (T⁺ : (s : S) → Orn u (T s)) → Orn u (`Σ S T)
  `Π : ∀{S T} → (T⁺ : (s : S) → Orn u (T s)) → Orn u (`Π S T)

  -- Delete
  deleteΣ : ∀{S T} → (s : S)
                     (T⁺ : Orn u (T s))  →
                    Orn u (`Σ S T)
  deleteσ : ∀{n T} → (k : Fin n)
                     (T⁺ : Orn u (T k))  →
                    Orn u (`σ n T)

-- Paper: Definition 4.1
⟦_⟧Orn : ∀{I K : Set}{u : I → K}{D : IDesc K} → Orn u D → IDesc  I
⟦ `1 ⟧Orn = `1
⟦ T⁺ `× T'⁺ ⟧Orn = ⟦ T⁺ ⟧Orn `× ⟦ T'⁺ ⟧Orn 
⟦ `σ {n} T⁺ ⟧Orn = `σ n ((λ D → ⟦ D ⟧Orn) ∘ T⁺)
⟦ `Σ {S} T⁺ ⟧Orn = `Σ S ((λ D → ⟦ D ⟧Orn) ∘ T⁺)
⟦ `Π {S} T⁺ ⟧Orn = `Π S ((λ D → ⟦ D ⟧Orn) ∘ T⁺)
⟦ `var (inv i⁺) ⟧Orn = `var i⁺
⟦ insert S D⁺ ⟧Orn = `Σ S (λ s → ⟦ D⁺ s ⟧Orn)
⟦ deleteΣ s T⁺ ⟧Orn = ⟦ T⁺ ⟧Orn 
⟦ deleteσ k T⁺ ⟧Orn = ⟦ T⁺ ⟧Orn  

{-
On paper, we define orn as

orn : ∀ {I J K L : Set}(D : func K L)(u : I → K)(v : J → L) → Set₁
orn {J = J} D u v = (j : J) → Orn u (func.out D (v j))

Here, we help the unification engine by keeping things folded:
-}

-- Paper: Definition 4.3
record orn {I J K L : Set}(D : func K L)(u : I → K)(v : J → L) : Set₁ where
  constructor mk
  field 
    out : (j : J) → Orn u (func.out D (v j))


⟦_⟧orn : {I J K L : Set}{D : func  K L}{u : I → K}{v : J → L}  → 
        orn D u v → func  I J
⟦ o ⟧orn = func.mk λ j → ⟦ orn.out o j ⟧Orn
