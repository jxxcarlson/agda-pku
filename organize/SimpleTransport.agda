{-# OPTIONS --cubical #-}

module SimpleTransport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Transport
open import Cubical.Data.Nat

-------------------------------------------------------------------------------
-- A small boolean type and a dependent family over it
-------------------------------------------------------------------------------

data Bool : Set where
  true  : Bool
  false : Bool

-- We define a family P : Bool → Set
--   * P true  = ℕ
--   * P false = Bool
P : Bool → Set
P true  = ℕ
P false = Bool

-------------------------------------------------------------------------------
-- A trivial path 'refl false' in Bool
-------------------------------------------------------------------------------

same-false : false ≡ false
same-false = refl false
  -- This is the reflexive path from 'false' to itself.

-------------------------------------------------------------------------------
-- An element in 'P false' is a Bool
-------------------------------------------------------------------------------

someElem : P false
someElem = true

-------------------------------------------------------------------------------
-- Demonstrate transport along the trivial path does nothing
-------------------------------------------------------------------------------

example-transport : transport P same-false someElem ≡ someElem
example-transport = refl _
  -- Because 'same-false' is the reflexive path, transporting 'someElem'
  -- along it yields 'someElem' again, so we can prove it by 'refl'.