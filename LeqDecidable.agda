module LeqDecidable where

open import Data.Nat hiding (_≤_)
open import Data.Bool hiding (_≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality as Eq
open import Data.Product

open import Data.Unit

-- Define bottom (⊥) as the empty type
-- ⊥ is the type of proofs of falsehood

-- Define decidability
data Dec (P : Set) : Set where
  yes : P → Dec P
  no  : (P → ⊥) → Dec P

-- Define less-than-or-equal
data _≤_ : ℕ → ℕ → Set where
  leZero : ∀ {n} → zero ≤ n
  leSucc : ∀ {m n} → m ≤ n → suc m ≤ suc n

-- Decidability of _≤_
dec≤ : (m n : ℕ) → Dec (m ≤ n)
dec≤ zero n = yes leZero
dec≤ (suc m) zero = no (λ ())
dec≤ (suc m) (suc n) with dec≤ m n
... | yes p = yes (leSucc p)
... | no ¬p = no (λ { (leSucc p) → ç˜¬p p })

test : 2 ≤ 4
test = leSucc (leSucc leZero)

test0 : (n : ℕ) → 0 ≤ n
test0 n = leZero

test1 : (n : ℕ) → Dec (1 ≤ n)
test1 zero = no λ()
test1 (suc n) = yes (leSucc leZero)

test2 : (n : ℕ) → Dec (2 ≤ n)
test2 zero = no λ()  -- 2 ≤ 0 is impossible
test2 (suc zero) = no λ { (leSucc p) → case1 p }  -- need helper lemma
  where
    case1 : 1 ≤ 0 → ⊥
    case1 ()
test2 (suc (suc n)) = yes (leSucc (leSucc leZero))


 