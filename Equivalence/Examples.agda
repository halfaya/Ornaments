{-# OPTIONS --without-K #-}

module Examples where

open import Data.Bool                             using (Bool; true; false; if_then_else_)
open import Data.Nat                              using (ℕ; zero; suc; _+_)

open import Equivalence
open import Pair
open import Functions

p : Pair Bool ℕ
p = true , 3

q : Pair ℕ Bool
q = swapEquiv ↑ p

maybeSuc : Pair Bool ℕ → ℕ
maybeSuc (b , n) = if b then suc n else n

maybeSuc' : Pair ℕ Bool → ℕ
maybeSuc' = f≃ swapEquiv ↑ maybeSuc 
