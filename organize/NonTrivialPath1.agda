{-# OPTIONS --cubical #-}

module NonTrivialPath where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
  using (iso; isoToEquiv)

------------------------------------------------------------------------
-- 1. Define 𝟚, the two-element type, and the flip involution
------------------------------------------------------------------------

data 𝟚 : Set where
  zero : 𝟚
  one  : 𝟚

swap : 𝟚 → 𝟚
swap zero = one
swap one  = zero

swapInv : 𝟚 → 𝟚
swapInv = swap

swapLeftInv : (x : 𝟚) → swapInv (swap x) ≡ x
swapLeftInv zero = refl
swapLeftInv one  = refl

swapRightInv : (x : 𝟚) → swap (swapInv x) ≡ x
swapRightInv zero = refl
swapRightInv one  = refl

------------------------------------------------------------------------
-- 2. Turn swap into an Equiv 𝟚 𝟚, then into a path 𝟚 ≡ 𝟚 via ua
------------------------------------------------------------------------

swapEquiv : 𝟚 ≃ 𝟚
swapEquiv = isoToEquiv (iso swap swapInv swapLeftInv swapRightInv)

nonTrivialPath : 𝟚 ≡ 𝟚
nonTrivialPath = ua swapEquiv
  -- This is the non-identity loop in 𝟚 : Set.

------------------------------------------------------------------------
-- 3. The family (λ X → X ≡ X), used for “transport of loops” in a type
------------------------------------------------------------------------

-- For each type X in the universe, we look at the type of loops X ≡ X.
-- This is the standard family used to show that transporting a loop
-- along an equality of types yields a loop in the new type.
Family : Set → Set₁
Family X = X ≡ X

------------------------------------------------------------------------
-- 4. Main lemma: transporting `refl 𝟚` along `nonTrivialPath` returns
--    `nonTrivialPath` itself, by the univalence β-rule.
------------------------------------------------------------------------

-- Statement:
--   transport (λ X → X ≡ X) (nonTrivialPath) (refl 𝟚)  ≡  nonTrivialPath
--
-- i.e. “Transport the trivial loop in 𝟚 = 𝟚 along the path 𝟚 ≡ 𝟚
--      coming from univalence. This yields the flip loop itself.”

transportPATH :
  transport Family nonTrivialPath (refl 𝟚)  ≡  nonTrivialPath
transportPATH =
  -- A single application of the univalence β-rule for identity types,
  -- often called `uaβ-type` or a similar name (depending on the version
  -- of the Cubical library). If your library doesn't expose that lemma
  -- directly, you can prove it by unfolding the definitions of ua, coe,
  -- and transport. For many versions of Cubical Agda, it's something like:
  --
  -- uaβ-type swapEquiv
  --
  -- If that doesn't work out-of-the-box, define or locate the lemma that
  -- states:  transport (λ X → X ≡ X) (ua e) (refl A) = ua e
  -- for any equivalence e : A ≃ A.
  --
  -- For illustration, we just inline the name:
  uaβ swapEquiv