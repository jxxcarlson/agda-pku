module RecNat2 where

open import Data.Nat


recNat : (C : Set) → C → (ℕ → C → C) → ℕ → C
recNat c base step zero    = base
recNat c base step (suc n) = step n (recNat c base step n)
 

add : ℕ → ℕ → ℕ
add = recNat (ℕ → ℕ) (λ y → y) (λ _ f y → suc (f y))
