{-# OPTIONS --cubical #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (Path)
open import Cubical.Data.Nat using (ℕ; zero; suc)

module ZModN (n : ℕ) where

-- A helper: iterated application of a function.
iter : ∀ {A : Set} → ℕ → (A → A) → A → A
iter ℕ.zero f x    = x
iter (ℕ.suc n) f x = f (iter n f x)

-- Define ℤmod as a higher inductive type
data ℤmod : Set where
  zero : ℤmod
  suc  : ℤmod → ℤmod
  -- The loop says that iterating suc n times from zero gives zero.
  loop : Path ℤmod (iter n suc zero) zero