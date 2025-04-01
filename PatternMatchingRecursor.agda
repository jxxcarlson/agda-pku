
module PatternMatchingRecursor where

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; _≡_)

-- The recursor for ℕ:
natElim : {P : Nat → Set} → P zero → ((n : Nat) → P n → P (suc n)) → (n : Nat) → P n
natElim base step zero    = base
natElim base step (suc n) = step n (natElim base step n)

-- Double function defined by pattern matching.
double : Nat → Nat
double zero    = zero
double (suc n) = suc (suc (double n))

-- Double function defined via the recursor.
double' : Nat → Nat
double' = natElim {P = λ _ → Nat} zero (λ n rec → suc (suc rec))

-- Proof that double and double' are definitionally the same.
doubleDouble' : (n : Nat) → double n ≡ double' n
doubleDouble' zero    = refl
doubleDouble' (suc n) = cong (λ m → suc (suc m)) (doubleDouble' n)



-- Define the sum of two natural numbers.
sum : Nat → Nat → Nat
sum zero m = m
sum (suc n) m = suc (sum n m)

-- Define the sum of two natural ners using the recursor.
sum' : Nat → Nat → Nat
sum' = natElim {P = λ _ → Nat → Nat} (λ m → m) (λ n rec m → suc (rec m))

-- Proof that sum and sum' are definitionally the same.
sumSum' : (n m : Nat) → sum n m ≡ sum' n m
sumSum' zero m = refl
sumSum' (suc n) m = cong (λ k → suc k) (sumSum' n m)