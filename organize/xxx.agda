module xxx where

open import Data.Nat
open import Data.Empty
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

left-identity : (x : ℕ) → (0 + x) ≡ x
left-identity zero = refl
left-identity (suc x) = refl

right-identity : (x : ℕ) → (x + 0) ≡ x
right-identity zero = refl
right-identity (suc x) = cong suc (right-identity x)

example : 1 ≡ 1
example = refl

example2 : 1 ≡ 2 → ⊥
example2 ()


_+_ : ℕ → ℕ → ℕ
zero + y = y
(suc x) + y = suc (x + y)
