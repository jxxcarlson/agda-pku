module RecNat where

open import Data.Nat


recNat : ∀ {C : Set} → C → (ℕ → C → C) → ℕ → C
recNat base step zero    = base
recNat base step (suc n) = step n (recNat base step n)
 

add : ℕ → ℕ → ℕ
add = recNat (λ y → y) (λ _ f y → suc (f y))
