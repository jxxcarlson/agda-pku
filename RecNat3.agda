module RecNat3 where

open import Data.Nat


recNat : (C : Set) → C → (ℕ → C → C) → ℕ → C
recNat c base step zero    = base
recNat c base step (suc n) = step n (recNat c base step n)
 

add : ℕ → ℕ → ℕ
add = recNat (ℕ → ℕ) (λ n → n) (λ _ g → (λ n → suc (g n)))






