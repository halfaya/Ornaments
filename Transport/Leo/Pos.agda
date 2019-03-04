{-# OPTIONS --without-K #-}

module Leo.Pos where

open import IDesc.Examples.Bool
open import IDesc.Examples.Nat
open import IDesc.Fixpoint
open import IDesc.IDesc
open import IDesc.InitialAlgebra

open import Orn.AlgebraicOrnament

open import Agda.Builtin.Unit

open import Data.Fin.Base using (zero; suc)
open import Data.Product

open import Relation.Binary.PropositionalEquality

-- α is a map from 1 + Bool → Bool
-- α maps _ : 1 → false and _ : Bool → true
α : Alg NatD (λ _ → Bool)
α {tt} (zero , tt)     = false
α {tt} (suc zero , _ ) = true
α (suc (suc ()) , _)

-- 0 is not positive; everything else is
isPos : Nat → Bool
isPos = fold NatD α

Pos : Set
Pos = Σ Nat (λ n → isPos n ≡ true)

ZeroPos : Set
ZeroPos = Σ Bool (λ b → Σ Nat (λ n → isPos n ≡ b))
