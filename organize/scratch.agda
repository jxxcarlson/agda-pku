{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism

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

-- The non-identity path 𝟚 ≡ 𝟚
nonTrivialPath : 𝟚 ≡ 𝟚
nonTrivialPath = ua (isoToEquiv 
   (iso swap swapInv swapLeftInv swapRightInv))

-- We define the family (X : Set) ↦ X ≡ X
Family : Set → Set₁
Family X = X ≡ X

-- Now we prove that transporting 𝟚 in the universe
-- along the path 'nonTrivialPath' equals 𝟚
transportPATH :
  transport (λ i → Set) 𝟚 ≡ 𝟚
transportPATH =
  uaβ (isoToEquiv (iso swap swapInv swapLeftInv swapRightInv)) (refl 𝟚)




-- The computation rule for ua. Because of "ghcomp" it is now very
-- simple compared to cubicaltt:
-- https://github.com/mortberg/cubicaltt/blob/master/examples/univalence.ctt#L202
-- uaβ : {A B : Type ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ equivFun e x
-- uaβ e x = transportRefl (equivFun e x)