open import Relation.Binary.PropositionalEquality

happly : {A : Set} {B : A -> Set} {f g : (x : A) -> B x} -> (f ≡ g) -> (x : A) -> f x ≡ g x
happly refl x = refl