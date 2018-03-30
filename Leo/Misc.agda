module Misc where

open import Data.Product

f : {I : Set} → Σ Set (λ (X : Set) → (X → I)) → (I → Set)
f {I} (X , x→i) = λ i → {!!}

g : {I : Set} → (I → Set) → Σ Set (λ (X : Set) → (X → I))
g {I} i→s = ({!!} , {!!})

--f∘g : {I : Set} → 
