------------------------------------------------------------------------
-- Definitions from The Agda standard library
------------------------------------------------------------------------

-- Data.Product

record Σ (A : Set) (B : A → Set) : Set where
  constructor _,_
  field
    proj₁ : A
    proj₂ : B proj₁

open Σ public

-- The syntax declaration below is attached to Σ-syntax, to make it
-- easy to import Σ without the special syntax.

infix 2 Σ-syntax

Σ-syntax : (A : Set) → (A → Set) → Set
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

∃ : ∀ {A : Set} → (A → Set) → Set
∃ = Σ _


-- Data.Empty

data ⊥ : Set where

⊥-elim : ∀ {Whatever : Set} → ⊥ → Whatever
⊥-elim ()

-- Data.Unit

record ⊤ : Set where
  constructor tt

-- Data.Nat

data ℕ : Set where
  zero : ℕ
  suc  : (n : ℕ) → ℕ

{-# BUILTIN NATURAL ℕ #-}

-- Data.Sum

infixr 1 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : (x : A) → A ⊎ B
  inj₂ : (y : B) → A ⊎ B

-- Relation.Binary.PropositionalEquality

infix 4 _≡_

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_ #-}
--{-# BUILTIN REFL refl #-}

subst : ∀ {a}{A : Set a} → (P : A → Set) → ∀{a b} → a ≡ b → P a → P b
subst P refl p = p

sym : ∀ {a} {A : Set a} → ∀{a b : A} → a ≡ b → b ≡ a
sym refl = refl

trans : ∀ {a} {A : Set a} → ∀{a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans refl eq = eq

cong : ∀ {a b} {A : Set a} {B : Set b}
       (f : A → B) {x y} → x ≡ y → f x ≡ f y
cong f refl = refl


subst₂ : ∀{A : Set} {B : A → Set} (P : (a : A) → B a → Set)
          {x₁ x₂ y₁} → (q : x₁ ≡ x₂) → P x₁ y₁ → P x₂ (subst B q y₁)
subst₂ P refl p = p


cong₃ : ∀{A : Set}{B : A → Set}{C : (a : A) → B a → Set}{D : Set}
        (f : (a : A)(b : B a) → C a b → D ) 
        {x y : A}{u : B x}{s : C x u} → 
        (qa : x ≡ y) → f x u s ≡ f y (subst B qa u) (subst₂ C qa s)
cong₃ f refl = refl

-- Function

id : ∀ {a} {A : Set a} → A → A
id x = x


_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
