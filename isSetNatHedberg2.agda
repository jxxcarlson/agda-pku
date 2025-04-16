open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (¬_; Decidable)

hedberg :
  ∀ {A : Set} →
  (∀ (x y : A) → (x ≡ y) ⊎ ¬ (x ≡ y)) →
  ∀ (x y : A) (p q : x ≡ y) → p ≡ q
hedberg dec x y p q with dec x y
... | inj₂ n = ⊥-elim (n p)  -- contradiction: we have a proof of x ≡ y
... | inj₁ e =                 -- now e, p, q : x ≡ y
  -- transport p over a constant family gives x,
  -- transport q gives x, so p and q must be equal
  let
    -- constant family: P z = x
    P : A → Set
    P z = x

    -- transport along p and q
    tp : P y
    tp = subst P p x

    tq : P y
    tq = subst P q x
  in
    cong (λ z → subst P z x) (uip e p q)

-- We still need to define uip, using identity induction:

uip :
  ∀ {A : Set} {x y : A} (r : x ≡ y) (p q : x ≡ y) → p ≡ q
uip refl p q = J (λ y r → ∀ p q : x ≡ y → p ≡ q)
                (λ p q → J (λ _ q → refl ≡ q)
                          (λ _ → refl)
                          x q)
                y r p q