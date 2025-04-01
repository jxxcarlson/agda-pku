{-# OPTIONS --cubical #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport

open import Cubical.Data.Nat
open import Cubical.Data.Integer

P : I → Type
P i0 = ℕ
P i1 = ℤ

example : ℕ → ℤ
example x = transp {A = P} x
