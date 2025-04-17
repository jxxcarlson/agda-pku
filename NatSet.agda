ℕ-isSet : isSet ℕ
ℕ-isSet x y p q = ℕ-UIP p q 

≡-normalise : ∀ {x y : ℕ} → x ≡ y → x ≡ y
≡-normalise {x} {y} x≡y = recompute (x ≟ y) x≡y 