module NoGood where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

f : ℕ → ℕ
f zero = zero
f (suc n) = f ( suc n)

