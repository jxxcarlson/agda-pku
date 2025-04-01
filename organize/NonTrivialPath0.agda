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
Id2 : (2 ≡ 2) → (2 ≡ 2)
Id2 q = q

-- Now we prove that transporting refl 𝟚 in the family Id2
-- along the path 'nonTrivialPath' equals 'nonTrivialPath'.
transportPATH :
  transport (λ i → nonTrivialPath i) (refl 𝟚) ≡ nonTrivialPath
transportPATH =
  uaβ (isoToEquiv (iso swap swapInv swapLeftInv swapRightInv)) (refl 𝟚)

 