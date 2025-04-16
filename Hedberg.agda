module Hedberg where

open import Level using (Level; zero)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- A type is a set if all equality proofs between any two values are equal
isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ (x y : A) (p q : x ≡ y) → p ≡ q

-- Helper lemma: if x ≡ x is decidable, any equality proof is equal to refl
refl-is-canonical : ∀ {ℓ} {A : Set ℓ} →
  (dec : ∀ x y → Dec (x ≡ y)) →
  ∀ (x : A) (p : x ≡ x) → p ≡ refl
refl-is-canonical dec x p with dec x x
... | yes r = J x p r
... | no ¬r = ⊥-elim (¬r refl)

-- Use the eliminator J to reduce any x ≡ x to refl
J : ∀ {ℓ} {A : Set ℓ} (x : A) → ∀ {p : x ≡ x} → x ≡ x → x ≡ x
J x refl r = refl  -- Only case needed since refl generates identity type

-- Main theorem: decidable equality implies isSet
hedberg : ∀ {ℓ} {A : Set ℓ} →
  (dec : ∀ x y → Dec (x ≡ y)) →
  isSet A
hedberg dec x y p q with dec x y
... | yes r =
  trans (refl-is-canonical dec x p)
        (sym (refl-is-canonical dec x q))
... | no ¬r = ⊥-elim (¬r p)