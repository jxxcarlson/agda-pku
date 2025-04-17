{-# OPTIONS --without-K #-}

module UIP2 where

open import Agda.Primitive using (Level; _⊔_)

private
  variable
    ℓ : Level
    A : Set ℓ

data _≡_ {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

-- Just one definition to demonstrate stuckness
stuck : {x y : A} → (p : x ≡ y) → p ≡ refl
stuck p = {! !}