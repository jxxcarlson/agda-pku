module Nat where


data ℕ : Set where
     zero : ℕ
     suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

infixr 10 _+_
_+_ : ℕ → ℕ → ℕ
0 + b = b
suc a + b = suc (a + b)


infix 20 _*_
_*_ : ℕ → ℕ → ℕ
0 * b = 0
(suc a) * b = b + a * b

