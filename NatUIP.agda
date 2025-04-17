{-# OPTIONS --cubical-compatible --safe #-}

module NatUIP where

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc; _≟_)
open import Relation.Binary.PropositionalEquality.Core
  using (_≡_; refl; sym; trans; cong)
open import Relation.Binary.PropositionalEquality.Properties
  using (trans-symˡ)
open import Relation.Binary.Definitions using (Irrelevant)
open import Relation.Nullary.Decidable.Core using (recompute)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Empty using (⊥-elim)

-- First, let's define what UIP means for natural numbers
ℕ-UIP : Irrelevant {A = ℕ} _≡_
ℕ-UIP p q = ≡-irrelevant p q
  where
    -- Helper function to normalize equality proofs
    ≡-normalise : ∀ {x y : ℕ} → x ≡ y → x ≡ y
    ≡-normalise {x} {y} x≡y = recompute (x ≟ y) x≡y

    -- Show that the normalization is constant
    ≡-normalise-constant : ∀ {x y : ℕ} (p q : x ≡ y) → ≡-normalise p ≡ ≡-normalise q
    ≡-normalise-constant p q = refl

    -- Show that the normalized proof is equal to the original proof
    ≡-canonical : ∀ {x y : ℕ} (p : x ≡ y) → trans (sym (≡-normalise refl)) (≡-normalise p) ≡ p
    ≡-canonical refl = trans-symˡ (≡-normalise refl)

    -- Finally, prove that any two proofs of equality are equal
    ≡-irrelevant : ∀ {x y : ℕ} (p q : x ≡ y) → p ≡ q
    ≡-irrelevant p q = trans (sym (≡-canonical p)) 
                    (trans (cong (trans _) (≡-normalise-constant p q)) 
                           (≡-canonical q))

-- Now we can show that natural numbers form a set
ℕ-isSet : ∀ {x y : ℕ} (p q : x ≡ y) → p ≡ q
ℕ-isSet = ℕ-UIP 