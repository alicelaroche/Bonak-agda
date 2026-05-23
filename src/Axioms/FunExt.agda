open import Prelude

module Axioms.FunExt where

open import Equiv

FunExt-Axiom : Typeω
FunExt-Axiom = ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
             → (f g : (a : A) → B a)
             → isEquiv (happly {f = f} {g = g})

module FE (axiom : FunExt-Axiom) where

  fe-≃ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
     → (f g : (x : A) → B x)
     → (f ≡ g) ≃ ((a : A) → f a ≡ g a)
  fe-≃ f g = happly , axiom f g

  funExt : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x}
         → ((x : A) → f x ≡ g x) → f ≡ g
  funExt = invEq (fe-≃ _ _)

  funExt-impl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : {x : A} → B x}
         → ({x : A} → f {x} ≡ g {x}) → (λ {x} → f {x}) ≡ (λ {x} → g {x})
  funExt-impl {A = A} {B} {f} {g} p = cong (λ f {x} → f x) (funExt (λ x → p))
 
  funExt-η : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} (p : f ≡ g) → funExt (happly p) ≡ p
  funExt-η p = retEq (fe-≃ _ _) p
  
  funExt-β : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x} (p : (x : A) → f x ≡ g x) → happly (funExt p) ≡ p
  funExt-β p = secEq (fe-≃ _ _) p

  funExt-subst : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'}
               → {f g : (x : A) → B x} (p : (x : A) → f x ≡ g x)
               → (a : A) {C : B a → Type ℓ''} (c : C (f a))
               → subst (λ - → C (- a)) (funExt p) c
               ≡ subst (λ - → C -) (p a) c
  funExt-subst p a {C = C} c =
    subst (λ - → C (- a)) (funExt p) c
     ≡⟨  subst-∘' (funExt p) c ⟩
    subst (λ - → C -) (happly (funExt p) a) c
     ≡⟨ cong (λ - → subst (λ - → C -) (- a) c) (funExt-β p) ⟩
    subst (λ - → C -) (p a) c ∎
