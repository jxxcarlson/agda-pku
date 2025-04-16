module Hedberg where

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- A type is a set if all equality proofs between any two values are equal
isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ (x y : A) (p q : x ≡ y) → p ≡ q

-- Helper: all proofs of equality are equal if they reduce to refl
normalize : ∀ {ℓ : Level} {A : Set ℓ} {x y : A} → (r : x ≡ y) → (s : x ≡ y) → s ≡ r
normalize refl refl = refl

-- Hedberg’s Theorem: decidable equality implies isSet
hedberg : ∀ {ℓ} {A : Set ℓ} →
  (dec : ∀ x y → Dec (x ≡ y)) →
  isSet A
hedberg dec x y p q with dec x y
... | yes r = trans (normalize r p) (sym (normalize r q))
... | no ¬r = ⊥-elim (¬r p)