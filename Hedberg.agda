module Hedberg where

open import Level using (Level; zero)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- A type is a set if all identity proofs between any two values are equal
isSet : ∀ {ℓ} (A : Set ℓ) → Set ℓ
isSet A = ∀ (x y : A) (p q : x ≡ y) → p ≡ q

-- Identity eliminator
J : ∀ {ℓ} {A : Set ℓ} {x y : A}
    (P : x ≡ y → Set ℓ) →
    (∀ r → P r) →
    ∀ (p : x ≡ y) → P p
J P f refl = f refl

-- Hedberg's Theorem
hedberg : ∀ {ℓ} {A : Set ℓ} →
  (dec : ∀ x y → Dec (x ≡ y)) →
  isSet A
hedberg dec x y p q with dec x y
... | yes r =
  trans (J (λ e → p ≡ e) (λ e → sym (J (λ e' → e ≡ e') (λ _ → refl) p)) r)
        (J (λ e → q ≡ e) (λ e → sym (J (λ e' → e ≡ e') (λ _ → refl) q)) r)
... | no ¬r = ⊥-elim (¬r p)