{-# OPTIONS --without-K #-}

module UIP4 where

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; J)
open import Data.Nat using (ℕ; zero; suc)

-- Proof of UIP using J with correct typing
uip : ∀ {A : Set} {x y : A} → (p q : x ≡ y) → p ≡ q
uip {A} {x} {y} p q = 
  J (λ y′ p′ → ∀ (q′ : x ≡ y′) → p′ ≡ q′)  -- outer motive
    (λ q′ →                                  -- base case when p is refl
      J {A = A} {x = x}                      -- explicit type parameters
        (λ y′ e → refl {x = x} ≡ e)         -- inner motive with fixed x
        refl                                 -- base case: refl ≡ refl
        q′)                                  -- apply to second path
    p                                        -- apply outer J to first path
    q                                        -- apply result to second path

-- Example showing it's stuck
stuck : ∀ {A : Set} {x : A} → uip refl refl ≡ refl
stuck = {!!}  -- Cannot be filled because uip refl refl doesn't compute to refl