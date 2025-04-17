ç
module isSetNatHedberg where

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
hedberg dec x y p q = {! !}

-- We still need to define uip, using identity induction:

-- UIP for natural numbers
uip : ∀ {m n : ℕ} → (p q : m ≡ n) → p ≡ q
uip {zero} {zero} p q with zero ≟ zero
... | inj₁ refl = {! !}   -- Here p q : zero ≡ zero
... | inj₂ ne = ⊥-elim (ne p)
uip {zero} {suc n} p q with zero ≟ suc n
... | inj₁ e = {! !}
... | inj₂ ne = ⊥-elim (ne p)
uip {suc m} {n} p q = {! !}