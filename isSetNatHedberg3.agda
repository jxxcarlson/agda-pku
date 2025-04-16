{-# OPTIONS --without-K #-}

module isSetNatHedberg3 where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

---------------------------------------------------------------------------
-- Decidable equality for ℕ
---------------------------------------------------------------------------
_≟_ : (m n : ℕ) → (m ≡ n) ⊎ ¬ (m ≡ n)
zero ≟ zero = inj₁ refl
zero ≟ suc n = inj₂ λ ()
suc m ≟ zero = inj₂ λ ()
suc m ≟ suc n with m ≟ n
... | inj₁ p = inj₁ (cong suc p)
... | inj₂ p = inj₂ λ q → p (suc-injective q)
  where
    suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

---------------------------------------------------------------------------
-- Postulate dec-refl
--
-- For any type A with decidable equality dec, this postulate states that
-- for every a : A the decision on a ≡ a is exactly inj₁ refl.
---------------------------------------------------------------------------
postulate
  dec-refl : ∀ {A : Set}
             (dec : ∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
             {a : A} → dec a a ≡ inj₁ refl

---------------------------------------------------------------------------
-- Canonicalization function.
--
-- Given a decidable equality dec, for any proof p : a ≡ b, we define
--
--     canon dec p
--
-- by case–analysis on dec a b.
---------------------------------------------------------------------------
canon :
  ∀ {A : Set}
    (dec : ∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
    {a b : A} →
    (p : a ≡ b) → a ≡ b
canon dec {a} {b} p with dec a b
... | inj₁ e = e
... | inj₂ n = ⊥-elim (n p)

---------------------------------------------------------------------------
-- Canonicalization equation.
--
-- For any a : A and p : a ≡ a we have:
--
--     p ≡ canon dec p
---------------------------------------------------------------------------
canon-eq :
  ∀ {A : Set}
    (dec : ∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
    {a : A} →
    (p : a ≡ a) → p ≡ canon dec p
canon-eq dec refl rewrite dec-refl dec {a} = refl

---------------------------------------------------------------------------
-- Hedberg's Theorem (UIP).
--
-- If a type A has decidable equality then any two proofs of equality
-- between two elements are equal.
---------------------------------------------------------------------------
hedberg :
  ∀ {A : Set}
    (dec : ∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
    → ∀ {a b : A} (p q : a ≡ b) → p ≡ q
hedberg {A = A₀} dec {a = a} {b = b} p q =
  trans (canon-eq dec p′) (sym (canon-eq dec q′))
  where
    p′ : a ≡ a
    p′ = trans (sym p) p

    q′ : a ≡ a
    q′ = trans (sym q) q

---------------------------------------------------------------------------
-- UIP for ℕ
--
-- Specialized to natural numbers using the decidable equality _≟_.
---------------------------------------------------------------------------
uip : ∀ {m n : ℕ} → (p q : m ≡ n) → p ≡ q
uip {m} {n} p q = hedberg _≟_ p q