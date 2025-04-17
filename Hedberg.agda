{-# OPTIONS --without-K #-}

module Hedberg where

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

-- A type is a set if all identity proofs between any two values are equal
isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ x y (p q : x ≡ y) → p ≡ q

-- Identity eliminator J
J : ∀ {ℓ} {A : Set ℓ} {x : A}
    (P : ∀ {y} → x ≡ y → Set ℓ)
    (base : P refl)
    → ∀ {y} (p : x ≡ y) → P p
J P base refl = base

-- Compare any p : x ≡ y to itself using J (UIP)
uip : ∀ {ℓ} {A : Set ℓ} {x y : A} (p : x ≡ y) → ∀ (q : x ≡ y) → p ≡ q
uip p q = J (λ q → p ≡ q) refl q

-- Hedberg's Theorem
hedberg : ∀ {ℓ} {A : Set ℓ}
  (dec : ∀ x y → Dec (x ≡ y)) →
  isSet A
hedberg dec x y p q with dec x y
... | yes _ = uip p q
... | no ¬r = ⊥-elim (¬r p)