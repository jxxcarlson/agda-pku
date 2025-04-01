{-# OPTIONS --cubical #-}

module ZModNHom where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude using (Path; _∙_)  -- Path composition is here
open import Cubical.Data.Nat using (ℕ)
open import ZModN 2 as Mod2
open import ZModN 4 as Mod4

-- Define the homomorphism
hom : Mod2.ℤmod → Mod4.ℤmod
hom Mod2.zero = Mod4.zero
hom (Mod2.suc x) = Mod4.suc (Mod4.suc (hom x))  -- maps 1 to 2
hom (Mod2.loop i) = Mod4.loop i  -- since 2+2=0 in Z/4, this should work

