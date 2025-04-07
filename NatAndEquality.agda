module NatAndEquality where

-- Define the natural numbers from scratch.

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + n = n
suc m + n = suc (m + n)

-- Define the identity type and the congruence property.

data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

cong : {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

-- Prove that for all n, n + 0 = n.

lemma : ∀ (n : ℕ) → (n + zero) ≡ n
lemma zero = refl
lemma (suc n) = cong suc (lemma n)




