{-# OPTIONS --without-K #-}

module isSetNatHedberg3 where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_)

-- Decidable equality for ℕ
_≟_ : (m n : ℕ) → (m ≡ n) ⊎ ¬ (m ≡ n)
zero ≟ zero = inj₁ refl
zero ≟ suc n = inj₂ λ()
suc m ≟ zero = inj₂ λ()
suc m ≟ suc n with m ≟ n
... | inj₁ p = inj₁ (cong suc p)
... | inj₂ p = inj₂ λ q → p (suc-injective q)
  where
    suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl

-- Hedberg's theorem
hedberg : ∀ {A : Set} 
  → (∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y))
  → ∀ (x y : A) → ∀ (p q : x ≡ y) → p ≡ q
hedberg dec x y p q = trans (κ-inj p) (sym (κ-inj q))
  where
    -- κ sends an arbitrary proof to a canonical one
    κ : {A : Set} -> ∀ {x y : A} (p : x ≡ y) → x ≡ y
    κ p with dec x y
    ... | inj₁ e = e
    ... | inj₂ n = ⊥-elim (n p)

    -- κ-inj shows that refl (the only constructor for =)
    -- is fixed by κ
    κ-inj : {A : Set} -> ∀ {x y : A} (p : x ≡ y) → p ≡ κ p
    κ-inj refl = refl

-- UIP for natural numbers
uip : ∀ {m n : ℕ} → (p q : m ≡ n) → p ≡ q
-- Case: zero ≡ zero
uip {zero} {zero} p q with zero ≟ zero
... | inj₁ refl = hedberg _≟ zero zero p q
... | inj₂ ne   = ⊥-elim (ne p)
-- Case: zero ≡ suc n is impossible
uip {zero} {suc n} p q with zero ≟ suc n
... | inj₁ ()  -- empty pattern: impossible branch.
... | inj₂ ne  = ⊥-elim (ne p)
-- Case: suc m ≡ n (do case analysis on n)
uip {suc m} {n} p q with n
... | zero = sym (uip (sym p) (sym q))
... | suc n′ = cong suc (uip (suc-injective p) (suc-injective q))
  where
    suc-injective : ∀ {m n} → suc m ≡ suc n → m ≡ n
    suc-injective refl = refl