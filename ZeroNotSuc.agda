module ZeroNotSuc where

open import Data.Nat
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality


zero≠suc : ∀ {n : ℕ} → zero ≡ suc n → ⊥
zero≠suc ()
