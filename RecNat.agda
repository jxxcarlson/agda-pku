module RecNat where

open import Data.Nat


recNat : ∀ {C : Set} → C → (ℕ → C → C) → ℕ → C
recNat base steo zero    = base
recNat base step (suc n) = step n (recNat base step n)

add : ℕ → ℕ → ℕ
add x = recNat x (λ _ y → suc y) 
