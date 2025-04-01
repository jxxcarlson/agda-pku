module EvenOdd where

open import Data.Nat
open import Relation.Binary.PropositionalEquality as Eq
open import Data.Empty




-- Sum type: logical disjunction
infixr 4 _⊎_

data _⊎_ (A B : Set) : Set where
  inj₁ : A → A ⊎ B
  inj₂ : B → A ⊎ B

-- Even and Odd predicates as inductive families
data Even : ℕ → Set where
  evenZero : Even 0
  evenSS   : ∀ {n} → Even n → Even (suc (suc n))

data Odd : ℕ → Set where
  oddOne : Odd 1
  oddSS  : ∀ {n} → Odd n → Odd (suc (suc n))

-- Decide whether a number is Even or Odd
evenOrOdd : (n : ℕ) → Even n ⊎ Odd n
evenOrOdd zero = inj₁ evenZero
evenOrOdd (suc zero) = inj₂ oddOne
evenOrOdd (suc (suc n)) with evenOrOdd n
... | inj₁ e = inj₁ (evenSS e)
... | inj₂ o = inj₂ (oddSS o)