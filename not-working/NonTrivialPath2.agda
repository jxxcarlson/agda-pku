{-# OPTIONS --cubical #-}

{-

  Lemma : Let $f : \mathbf

-}

module NonTrivialPath2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
  using (iso; isoToEquiv)

-----------------------------------------------------------------------
-- 1. Define 𝟚, the two-element type, and the flip involution
-----------------------------------------------------------------------

data 𝟚 : Type₀ where
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

-----------------------------------------------------------------------
-- 2. Turn swap into an Equiv 𝟚 𝟚, then into a path 𝟚 ≡ 𝟚 via ua
-----------------------------------------------------------------------

swapEquiv : 𝟚 ≃ 𝟚
swapEquiv = isoToEquiv (iso swap swapInv swapLeftInv swapRightInv)

nonTrivialPath : 𝟚 ≡ 𝟚
nonTrivialPath = ua swapEquiv
  -- This is the non-identity loop in 𝟚, given by univalence.

-----------------------------------------------------------------------
-- 3. The family (λ X → X ≡ X) for "transport of loops"
-----------------------------------------------------------------------

Family : (X : Type₀) → Type₁
Family X = X ≡ X

-----------------------------------------------------------------------
-- 4. Main lemma:  transport Family nonTrivialPath (refl 𝟚) ≡ nonTrivialPath
-----------------------------------------------------------------------
-- That is, "transporting the trivial loop in 𝟚=𝟚 along the flip path
--  yields the flip path."
--
-- We rely on the β-rule for univalence, typically called `uaβ-type`,
-- which states:
--    transport (λ X → X ≡ X) (ua e) (refl A)  ≡  ua e
-- for e : A ≃ A.

transportPATH : transport Family nonTrivialPath (refl 𝟚) ≡ nonTrivialPath
transportPATH =
  -- Different library versions name this lemma differently:
  -- e.g. `uaβ-type swapEquiv` or `uaβ swapEquiv`.
  --
  -- If your library doesn't have it, you'll need to define
  -- or prove it yourself by unfolding 'transport' and 'ua'.
  uaβ swapEquiv