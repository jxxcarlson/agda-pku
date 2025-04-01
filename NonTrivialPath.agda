{-# OPTIONS --cubical #-}

{-

  Implement the argument of page 142 of the Hott Book to construct
  a non-trivial path between 𝟚 and itself.

-}

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

-- Construct a non-trivial path between 𝟚 and itself
nonTrivialPath : 𝟚 ≡ 𝟚
nonTrivialPath = ua (isoToEquiv
   (iso swap swapInv swapLeftInv swapRightInv))

-- Prove that transporting zero along this path gives one
transportZero : transport (λ i → nonTrivialPath i)
                zero ≡ one
transportZero = refl

-- Prove that transporting one along this path gives zero
transportOne : transport (λ i → nonTrivialPath i)
               one ≡ zero
transportOne = refl
