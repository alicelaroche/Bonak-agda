open import Prelude

module Axioms.Univalence where

open import Equiv

pathToEquiv : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A ≃ B
pathToEquiv {A = A} {B} p = f , ((g , g∘f∼id) , (g , f∘g∼id))
 where
 f : A → B
 f = transport p
 
 g : B → A
 g = transport (sym p)

 g∘f∼id : g ∘ f ∼ id
 g∘f∼id = subst-sym-l p

 f∘g∼id : f ∘ g ∼ id
 f∘g∼id = subst-sym-r p

Univalence-Axiom : Typeω
Univalence-Axiom = ∀ {ℓ} {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B = B})

module UA
 (ua-axiom : ∀ {ℓ} {A B : Type ℓ} → isEquiv (pathToEquiv {A = A} {B = B}))
 where 
  univalence : ∀ {ℓ} {A B : Type ℓ} → (A ≡ B) ≃ (A ≃ B)
  univalence = pathToEquiv , ua-axiom

  ua : ∀ {ℓ} {A B : Type ℓ} → A ≃ B → A ≡ B
  ua = invEq univalence

  ua-β : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → transport (ua e) ≡ equivFun e
  ua-β e = cong equivFun (secEq univalence e) 

  ua-η : ∀ {ℓ} {A B : Type ℓ} (p : A ≡ B) → ua (pathToEquiv p) ≡ p
  ua-η p = retEq univalence p

  ≃ind : ∀ {ℓ ℓ'} (P : {A B : Type ℓ} → (A ≃ B) → Type ℓ') →
         ({A : Type ℓ} → P (≃id A)) →
         {A B : Type ℓ} (e : A ≃ B) → P e
  ≃ind P p≃id e = subst P (secEq univalence e) I
   where
   I : P (pathToEquiv (ua e))
   I = J (λ _ - → P (pathToEquiv -)) p≃id (ua e) 

  ua-id : ∀ {ℓ} {A : Type ℓ} → ua (≃id A) ≡ refl
  ua-id {A = A} =
   ua (≃id A)
     ≡⟨⟩
   ua (pathToEquiv refl)
     ≡⟨ ua-η refl ⟩
   refl ∎

  ua-sym : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → sym (ua e) ≡ ua (≃sym e)
  ua-sym {ℓ} e = ≃ind (λ - → sym (ua -) ≡ ua (≃sym -)) I e
   where
   I : {A : Type ℓ} →  sym (ua (≃id A)) ≡ ua (≃sym (≃id A))
   I {A} =
    sym (ua (≃id A))
      ≡⟨ cong sym ua-id ⟩
    refl
      ≡⟨ ua-id ⟩⁻¹
    ua (≃id A)
      ≡⟨⟩
    ua (≃sym (≃id A)) ∎

  ua-β' : ∀ {ℓ} {A B : Type ℓ} (e : A ≃ B) → transport (sym (ua e)) ≡ invEq e
  ua-β' e =
    transport (sym (ua e))
      ≡⟨ cong transport (ua-sym e) ⟩
    transport (ua (≃sym e))
      ≡⟨ ua-β (≃sym e) ⟩
    invEq e ∎

