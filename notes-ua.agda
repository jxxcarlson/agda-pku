uaβ : {A B : Type ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ equivFun e x
uaβ e x = transportRefl (equivFun e x)

~uaβ : {A B : Type ℓ} (e : A ≃ B) (x : B) → transport (sym (ua e)) x ≡ invEq e x
~uaβ e x = cong (invEq e) (transportRefl x)

uaη : ∀ {A B : Type ℓ} → (P : A ≡ B) → ua (pathToEquiv P) ≡ P
uaη {A = A} {B = B} P i j = Glue B {φ = φ} sides where
  -- Adapted from a proof by @dolio, cf. commit e42a6fa1
  φ = i ∨ j ∨ ~ j

  sides : Partial φ (Σ[ T ∈ Type _ ] T ≃ B)
  sides (i = i1) = P j , transpEquiv (λ k → P k) j
  sides (j = i0) = A , pathToEquiv P
  sides (j = i1) = B , idEquiv B

pathToEquiv-ua : {A B : Type ℓ} (e : A ≃ B) → pathToEquiv (ua e) ≡ e
pathToEquiv-ua e = equivEq (funExt (uaβ e))

ua-pathToEquiv : {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
ua-pathToEquiv = uaη




Depending on which version of Cubical Agda or Cubical library you have, there is often a lemma named something like:
	•	uaβ-id,
	•	uaβ-type,
	•	ua-β-id-loop, or
	•	uaβ-refl,

which states exactly:


  transport (λ X → X ≡ X) (ua e) (refl A)  ≡  ua e

If your library supplies one of these, simply replace:

   transportPATH = uaβ swapEquiv

with 


transportPATH = uaβ-id 𝟚 swapEquiv

-- or whichever name your library uses
-- e.g. uaβ-type swapEquiv


uaβ : {A B : Type ℓ} (e : A ≃ B) (x : A) → transport (ua e) x ≡ equivFun e x
uaβ e x = transportRefl (equivFun e x)

--Have: {??}

uaβ : {A B : Type ℓ} (e : A ≃ B) (x : A) → transport (λ X → X) (ua e) x ≡ e x

-- Need: 

uaβ-id : (A : Type ℓ) (e : A ≃ A)
       → transport (λ X → X ≡ X) (ua e) (refl A)
       ≡ ua e