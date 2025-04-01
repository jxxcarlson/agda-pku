module ModusPonens where

-- We assume P and Q are arbitrary types (propositions).
-- In Agda, propositions are represented as types.
modusPonens : ∀ {P Q : Set} → (P → Q) → P → Q
modusPonens f p = f p