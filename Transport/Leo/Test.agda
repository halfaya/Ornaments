{-# OPTIONS --without-K #-}

module Leo.Test where

open import Data.Fin
open import IDesc.IDesc
open import IDesc.Examples.Nat
open import IDesc.Fixpoint
open import Agda.Builtin.Sigma
open import Agda.Builtin.Unit

zer : Nat
zer = ⟨ zero , tt ⟩

onee : Nat
onee = ⟨ suc zero , ⟨ (zero , tt) ⟩ ⟩

one : Nat
one = su ze

two : Nat
two = su one
