{-# OPTIONS --without-K #-}

module SymmetryProofWithJ where

open import Agda.Primitive using (Level; _⊔_)

private
  variable
    ℓ : Level
    A : Set ℓ

-- Standard equality type
data _≡_ {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

-- The J eliminator
J : ∀ {ℓ' : Level} 
    (P : (x y : A) → x ≡ y → Set ℓ') →
    ((x : A) → P x x refl) →
    (x y : A) → (p : x ≡ y) → P x y p
J P d x .x refl = d x

-- Symmetry proof
sym : {x y : A} → x ≡ y → y ≡ x
sym {x = x} {y = y} = J (λ a b _ → b ≡ a) (λ x → refl) x y