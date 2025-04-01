module NatProofs where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Empty using (⊥)

-- Natural numbers (Peano definition)
data ℕ : Set where
  zero : ℕ
  succ : ℕ -> ℕ

{-# BUILTIN NATURAL ℕ  #-}

-- Addition on natural numbers
_+_ : ℕ -> ℕ -> ℕ
zero    + n = n
succ m + n = succ (m + n)

-- Multiplication on natural numbers
_*_ : ℕ -> ℕ -> ℕ
zero    * n = zero
succ m * n = n + (m * n)

-- Less-than-or-equal relation (≤) on ℕ
data _≤_ : ℕ -> ℕ -> Set where
  z≤n : ∀ {n}   -> zero ≤ n                -- 0 is ≤ any n
  s≤s : ∀ {m n} -> m ≤ n -> succ m ≤ succ n

-- We use Agda's built-in propositional equality `≡` (with proof constructor `refl`).
-- `x ≡ y` is the type of proofs that x and y are equal.


-- PROBLEM 1
-- Prove that 0 is not equal to the successor of any natural number. 
-- In other words, for every `n : ℕ`, there is no proof of `zero ≡ succ n`.

zero≠succ : ∀ {n : ℕ} -> zero ≡ succ n -> ⊥
zero≠succ ()  -- no pattern for this case, it's impossible to have zero = succ n


-- PROBLEM 2
-- Prove that the successor constructor is **injective**. 
-- Formally, for all `m n : ℕ`, if `succ m ≡ succ n` then `m ≡ n`.

succInjective : ∀ {m n : ℕ} -> succ m ≡ succ n -> m ≡ n
succInjective refl = refl


-- PROBLEM 3
-- Prove that 0 is the Identity for Addition.
-- Formally, for all `n : ℕ`, `n + zero ≡ n`.
--
--  Show that:
-- - (a) `0 + n ≡ n` (left identity)
-- - (b) `n + 0 ≡ n` (right identity)

-- (a) 0 + n ≡ n  (left identity of addition)
plusZeroLeft : ∀ (n : ℕ) -> zero + n ≡ n
plusZeroLeft n = refl

-- (b) n + 0 ≡ n  (right identity of addition)
plusZeroRight : ∀ (n : ℕ) -> n + 0 ≡ n
plusZeroRight 0 = refl
plusZeroRight (succ n) = cong succ (plusZeroRight n)




-- PROBLEM 4
-- Prove that addition is **associative**: 
-- for all `a, b, c : ℕ`, `(a + b) + c ≡ a + (b + c)`.


plusAssoc : ∀ (a b c : ℕ) -> (a + b) + c ≡ a + (b + c)
plusAssoc 0 b c = refl
plusAssoc (succ a) b c = 
  cong succ (plusAssoc a b c)


-- Problem 5: Addition is Commutative  
-- Prove that addition is **commutative**: 
-- for all `a, b : ℕ`, `a + b ≡ b + a`.

-- We first prove a helper lemma:
-- Helper Lemma: adding a successor on the right
plusSuccRight : ∀ (x y : ℕ) -> x + (succ y) ≡ succ (x + y)
plusSuccRight 0       y = refl
plusSuccRight (succ x) y = cong succ (plusSuccRight x y)


-- Now, the main proof:

plusComm : ∀ (a b : ℕ) -> a + b ≡ b + a
plusComm zero b rewrite plusZeroRight b = refl
plusComm (succ a) b rewrite plusSuccRight b a | plusComm a b = refl




-- PROBLEM  6  
-- Prove that 1 (defined as `succ zero`) is the **multiplicative identity**: 
-- for all `n : ℕ`, `1 * n ≡ n` and `n * 1 ≡ n`.


-- (a) 1 * n ≡ n  (left identity for multiplication)
timesOneLeft : ∀ (n : ℕ) -> (succ zero) * n ≡ n
timesOneLeft 0       = refl
timesOneLeft (succ m) rewrite plusZeroRight m = refl

-- (b) n * 1 ≡ n  (right identity for multiplication)
timesOneRight : ∀ (n : ℕ) -> n * (succ zero) ≡ n
timesOneRight 0       = refl
timesOneRight (succ m) rewrite timesOneRight m = refl




-- PROBLEM 7
-- Prove that addition is **monotonic** with respect to the ≤ relation. 
-- Specifically, for all `a, b, c : ℕ`, if `a ≤ b` then `a + c ≤ b + c`.

monotonicAdd : ∀ (a b c : ℕ) -> a ≤ b -> (a + c) ≤ (b + c)
monotonicAdd a b zero p rewrite plusZeroRight a | plusZeroRight b = p
monotonicAdd a b (succ c) p rewrite plusSuccRight a c | plusSuccRight b c = 
  s≤s (monotonicAdd a b c p)





-- PROBLEM 8. Structural Recursion Example – Double a Number
-- Define a function `double : ℕ -> ℕ` that doubles a natural number, 
-- and prove that it equals adding the number to itself, i.e., `double n ≡ n + n` for all `n`.


-- Define the double function
double : ℕ -> ℕ
double 0        = 0
double (succ n) = succ (succ (double n))

-- Prove double n equals n + n
doubleCorrect : ∀ (n : ℕ) -> double n ≡ n + n
doubleCorrect 0 = refl
doubleCorrect (succ n) rewrite doubleCorrect n | plusSuccRight n n = refl

