module NatAndEquality where

-- 1. Define the natural numbers from scratch.
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

-- 2. Define the addition operation.
_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- 3. Define the identity type.
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

lemma : ∀ (n : ℕ) → (n + zero) ≡ n
lemma zero = refl
lemma (suc n) = cong suc (lemma n)

