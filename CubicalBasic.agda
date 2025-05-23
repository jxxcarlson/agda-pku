{-# OPTIONS --cubical #-}

-- /Users/carlson/dev/agda/cubical/Cubical/Foundations/Prelude.agda

module CubicalBasic where

open import Cubical.Core.Everything
open import Cubical.Foundations.Prelude hiding (funExt)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Isomorphism
open import Relation.Binary.PropositionalEquality hiding(_≡_; refl; cong)
open import Data.Bool hiding(not)
open import Data.Empty
open import Relation.Nullary

variable 
    A B : Set

-- A path from a to b in A
pathExample : (A : Set) → (a b : A) → Path A a b → A
pathExample A a b p = p i0  -- evaluates to `a`

-- The identity path, i.e. the constantpath from a to a
pathId : ∀ {A : Set} (a : A) → Path A a a
pathId a i = a

-- Function extensionality is a library function,
-- but we can hide it and implement it ourselves:
funExt : ∀ {A B : Set} (f g : A → B) →
         (∀ x → Path B (f x) (g x)) →
         Path (A → B) f g
funExt f g p i x = p x i

-- The not equivalence on Bool
notEquiv : Bool ≃ Bool
notEquiv = isoToEquiv (iso not not not-involutive not-involutive)
  where
    not : Bool → Bool
    not true = false
    not false = true
    
    not-involutive : (b : Bool) → not (not b) ≡ b
    not-involutive true = refl
    not-involutive false = refl

-- Two different paths between Bool and itself
path1 : Path (Set) Bool Bool
path1 = refl

path2 : Path (Set) Bool Bool
path2 = ua notEquiv

-- Proof that Set is not a set (see HoTT book page 142)
Set-is-not-set : ¬ (∀ (A B : Set) (p q : Path (Set) A B) → p ≡ q)
Set-is-not-set isSet = false≢true (transport-path-eq path-eq)
  where
    -- Extract the value at i0 from a path in Set
    f : Path (Set) Bool Bool → Bool
    f p = transport (λ i → p i) true
    
    -- If path1 ≡ path2, then their transported values must be equal
    path-eq : path1 ≡ path2
    path-eq = isSet Bool Bool path1 path2
    
    -- Helper function to get the path between transported values
    transport-path-eq : path1 ≡ path2 → Path Bool (transport (λ i → path1 i) true) (transport (λ i → path2 i) true)
    transport-path-eq p i = transport (λ j → p i j) true
    
    -- But path1 transports true to true, while path2 transports true to false
    false≢true : Path Bool true false → ⊥
    false≢true p = transport (λ i → if p i then Bool else ⊥) false

univalenceExample :
  ∀ {A B : Set} → (e : A ≃ B) → Path (Set) A B
univalenceExample = ua


-- I've fixed the contradiction proof using cubical primitives. Here's what changed:
-- Changed the type of false≢true to use Path Bool false true instead of false ≡ true
-- Instead of using the empty pattern (), we now use transport to create a contradiction:
-- We create a path that maps false to Bool and true to ⊥
-- When we transport false along this path, we get a value in ⊥ if the path p goes from 
-- false to true
-- This is a contradiction because we can't have a value in ⊥
-- This is a more explicit way to show the contradiction in cubical type theory. 
-- The key idea is that we can use transport to create a path-dependent type 
-- that becomes ⊥ when we have a path from false to true.



-- I've fixed the proof by:
-- Adding a helper function transport-path-eq that properly converts
--  the equality of paths into a path between the transported values
-- Using this helper function instead of cong f path-eq
-- The key insight is that we need to be more explicit about how 
-- the equality of paths relates to the equality of the transported values. 
-- The helper function transport-path-eq does this by:
-- Taking a path between path1 and path2
-- Applying f (which is transport along the path) to each point along this path
-- This gives us a path between f path1 (which is true) and f path2 (which is false)
-- This should now type check correctly. The proof shows that if 
-- Set were a set, we would have a path from false to true in Bool, 
-- which is impossible.