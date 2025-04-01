module LawOfNonContradiction where

open import Data.Product    -- For Σ types (pairs)
open import Data.Empty      -- For ⊥ (the empty type)

-- Define negation: ¬P is defined as P → ⊥
¬ : Set → Set
¬ P = P → ⊥

-- The law of non-contradiction states that for any proposition P,
-- the type P × ¬P is uninhabited.
-- In other words, we can prove:
--   ∀ {P : Set} → ¬ (Σ P (λ _ → ¬ P))
--
-- This means: given a pair (p , np) where p : P and np : P → ⊥,
-- we can derive ⊥ by applying np to p.
nonContradiction : ∀ {P : Set} → ¬ (Σ P (λ _ → ¬ P))
nonContradiction (p , np) = np p
