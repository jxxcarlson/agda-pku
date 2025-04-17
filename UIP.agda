{-# OPTIONS --without-K #-}


module UIP where

open import Data.Bool
-- open import IdentityType using (_≡_; refl; cong; subst; subst2)
open import Agda.Primitive using (Level; _⊔_)
open import Data.Nat using (ℕ)

private
  variable
    ℓ : Level
    A : Set ℓ


-- Identity type
data _≡_ {ℓ : Level} {A : Set ℓ} (x : A) : A → Set ℓ where
  refl : x ≡ x

-- Symmetry
sym : {x y : A} → x ≡ y → y ≡ x
sym refl = refl

-- Transitivity
trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl

-- Congruence
cong : { A B : Set ℓ} → {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

-- Substitution
subst : {x y : A} → (P : A → Set ℓ) → x ≡ y → P x → P y
subst P refl px = px

postulate -- UIP states that any two proofs of identity are themselves equal
  UIP : ∀ {ℓ} {A : Set ℓ} {x y : A} (p q : x ≡ y) → p ≡ q


-- A simple proof that 2 ≡ 2 using refl
example1 : 2 ≡ 2
example1 = refl

-- Another "proof" that 2 ≡ 2 using refl again
example2 : 2 ≡ 2
example2 = refl

-- Try to use UIP to show that example1 and example2 are equal
equality-of-equalities : example1 ≡ example2
equality-of-equalities = UIP example1 example2

-- Let's try to "compute" this
test : example1 ≡ example2
test = equality-of-equalities

-- stuck : ∀ {x y : ℕ} → (p : x ≡ y) → UIP p p ≡ refl
-- stuck p = refl   -- This should fail because UIP p p is stuck
 