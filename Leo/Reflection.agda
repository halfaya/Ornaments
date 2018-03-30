module Leo.Reflection where

open import Agda.Builtin.Reflection
open import Data.Fin
open import Data.Nat
open import Data.List
open import Data.String
open import Data.Unit
open import Function

open import Leo.Signature hiding (_∘_)

infixl 1 _≫=_

_≫=_ : ∀ {a b} {A : Set a} {B : Set b} → TC A → (A → TC B) → TC B
_≫=_ = bindTC

err : {A : Set} → String → TC A
err = typeError ∘ map strErr ∘ (λ x → "Error:\n" ∷ x ∷ [])

⊤term : Term
⊤term = quoteTerm ⊤

⊤name : Name
⊤name = quote ⊤

sort : Term → Name
sort (var x args)      = ⊤name
sort (con c args)      = ⊤name
sort (def f args)      = ⊤name
sort (lam v t)         = ⊤name
sort (pat-lam cs args) = ⊤name
sort (agda-sort s)     = ⊤name
sort (lit l)           = ⊤name
sort (meta x x₁)       = ⊤name
sort unknown           = ⊤name

sort (pi (arg _ (lam v t)) _)         = ⊤name
sort (pi (arg _ (var x args)) _)      = ⊤name
sort (pi (arg _ (pat-lam cs args)) _) = ⊤name
sort (pi (arg _ (pi a b)) _)          = ⊤name
sort (pi (arg _ (agda-sort s)) _)     = ⊤name
sort (pi (arg _ (lit l)) _)           = ⊤name
sort (pi (arg _ (meta x x₁)) _)       = ⊤name
sort (pi (arg _ unknown) _)           = ⊤name

sort (pi (arg _ (con c args)) _)      = c
sort (pi (arg _ (def f args)) _)      = f

macro
  getTyp : Name → Term → TC ⊤
  getTyp n hole = getType n ≫= unify hole

  getTyp2 : Name → Term → TC ⊤
  getTyp2 n hole = getType n ≫= quoteTC ≫= unify hole

  getSort : Name → Term → TC ⊤
  getSort n hole = getType n ≫= getType ∘ sort ≫= unify hole



--------

u : Term
u = getTyp2 Fin

