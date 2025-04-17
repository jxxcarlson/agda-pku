module UIP3 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; J)
open import Data.Nat using (ℕ; zero; suc)

postulate
  -- Axiom K: every self‑equality proof is reflexivity
  K : ∀ {A : Set} (x : A) (r : x ≡ x) → r ≡ refl

-- This version will fail with the error you saw:
bad-uip : ∀ {A : Set} {x y : A} (p q : x ≡ y) → p ≡ q
bad-uip {x = x} {x} refl q = {!!}  -- Error: x != x₁

-- First, let's define a helper lemma for paths to themselves
refl-unique : ∀ {ℓ} {A : Set ℓ} {x : A} → (p : x ≡ x) → refl ≡ p
refl-unique {ℓ} {A} {x} p = 
  J (λ _ q → refl ≡ q)  -- Use _ to avoid endpoint issues
    refl
    p

-- Now UIP using the helper
uip : ∀ {ℓ} {A : Set ℓ} {x y : A} → (p q : x ≡ y) → p ≡ q
uip {ℓ} {A} {x} {y} p q =
  J (λ y′ p′ → ∀ q′ → p′ ≡ q′)          -- motive
    (λ q′ →                              -- base case (when p is refl)
      J (λ y′′ q′′ → refl {x = x} ≡ q′′) -- inner motive
        refl                             -- inner base case
        q′)                              -- apply to q′
    p                                    -- apply outer J to p
    q                                    -- apply result to q

-- Now we can use trans in our proofs
example : ∀ {A : Set} {x y z : A} → (p : x ≡ y) → (q : y ≡ z) → x ≡ z
example p q = trans p q

-- Demonstrates that computation is stuck
stuck : ∀ {A : Set} {x : A} → uip refl refl ≡ refl
stuck = {!!}  -- Cannot be filled because uip refl refl is stuck