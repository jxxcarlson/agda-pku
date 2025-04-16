{-# OPTIONS --without-K #-}

module isSetNatHedberg3 where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

---------------------------------------------------------------------------
-- A simple transport function.
-- Given a family P over A, if x ≡ y then any element of P x can be
-- transported to an element of P y.
---------------------------------------------------------------------------
transport :
  ∀ {A : Set} {P : A → Set} {x y : A} → x ≡ y → P x → P y
transport refl p = p

---------------------------------------------------------------------------
-- Decidable equality for ℕ.
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
-- Postulate dec-refl.
-- For any type A with a decidable equality dec, this states that for every
-- a : A the decision on a ≡ a is exactly inj₁ refl.
---------------------------------------------------------------------------
postulate
  dec-refl : ∀ {A : Set}
             (dec : ∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
             {a : A} → dec a a ≡ inj₁ refl

---------------------------------------------------------------------------
-- Canonicalization.
--
-- Given a decidable equality dec, for any proof p : a ≡ b we “canonicalize”
-- it by case–analysis on dec a b.
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
-- For any proof p : a ≡ a we show that p is equal to its canonical form.
-- (Here we make the base point explicit to get "a" in scope.)
---------------------------------------------------------------------------
canon-eq :
  ∀ {A : Set}
    (dec : ∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
    (a : A) →
    (p : a ≡ a) → p ≡ canon dec p
canon-eq dec a refl rewrite dec-refl dec {a = a} = refl

---------------------------------------------------------------------------
-- Hedberg's Theorem (UIP).
--
-- If a type A has decidable equality then any two proofs of equality between
-- two elements are equal.
--
-- The idea is to “rebase” an arbitrary equality proof p : a ≡ b to a proof
-- of a reflexive equality on a. Here we use transport to convert any p : a ≡ b
-- into a proof of a ≡ a, and then apply canon-eq.
---------------------------------------------------------------------------
hedberg :
  ∀ {A : Set}
    (dec : ∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
    → ∀ {a b : A} (p q : a ≡ b) → p ≡ q
hedberg dec {a} {b} p q =
  let
    -- Using transport along p, we “rebase” p to a reflexive proof:
    p′ : a ≡ a
    p′ = transport (λ x → a ≡ x) p p

    q′ : a ≡ a
    q′ = transport (λ x → a ≡ x) q q
  in trans (canon-eq dec a p′) (sym (canon-eq dec a q′))

---------------------------------------------------------------------------
-- UIP for ℕ.
--
-- Specialize Hedberg's theorem to ℕ using the decidable equality _≟_.
---------------------------------------------------------------------------
uip : ∀ {m n : ℕ} → (p q : m ≡ n) → p ≡ q
uip {m} {n} p q = hedberg _≟_ p q