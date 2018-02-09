module Leo.Nat where

open import Stdlib

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)
