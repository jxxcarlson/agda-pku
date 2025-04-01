module NonContradictionNoSigma where

open import Data.Empty using (⊥)
open import Data.Product using (_,_;_×_)

-- Define negation as usual: ¬P is P → ⊥
¬ : Set → Set
¬ P = P → ⊥

-- Define our own conjunction as a record.
-- record _∧_ (P Q : Set) : Set where
--   constructor _,_
--   field
--     fst : P
--     snd : Q

-- open _∧_

-- The law of non-contradiction states that P and ¬P cannot both hold.
-- In our setting, this is:
--    ∀ {P : Set} → ¬ (P ∧ ¬P)
--
-- That is, assuming we have both a proof p : P and a proof np : P → ⊥,
-- we can derive ⊥.
nonContradiction : ∀ {P : Set} → (P × ¬ P) → ⊥
nonContradiction (p , np) = np p