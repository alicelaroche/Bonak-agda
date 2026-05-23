open import Prelude

module Category  (arity : Type) where

open import HSet
open import Inequalities

record Presheaf : Type₁ where
  field
    F0 : ℕ → HSet
    Face : ∀ n p {δ} → [ p ≤ n ][ δ ]₂ → arity → F0 (1+ n) .Dom → F0 n .Dom
    Face-coh : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃) 
             → (ε ω : arity)
             → (X : F0 (2+ n) .Dom)
             → Face n q (drop₃-1 p≤q≤n) ε (Face (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω X) 
             ≡ Face n p (drop₃-2 p≤q≤n) ω (Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε X)
open Presheaf public

Presheaf-≡' : ∀ psh psh'
           → (p : psh .F0 ≡ psh' .F0)
           → (q : subst (λ - → ∀ n p {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom) p (psh .Face)
                ≡ psh' .Face)
           → subst (λ - → ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃) 
                        → (ε ω : arity)
                        → (X : psh' .F0 (2+ n) .Dom)
                        → - n q (drop₃-1 p≤q≤n) ε (- (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω X) 
                        ≡ - n p (drop₃-2 p≤q≤n) ω (- (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε X))
             q (dsubst
                 (λ - → ∀ n p {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
                 (λ -₁ -₂ → ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃) 
                    → (ε ω : arity)
                    → (X : -₁ (2+ n) .Dom)
                    → -₂ n q (drop₃-1 p≤q≤n) ε
                      (-₂ (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω X)
                    ≡ -₂ n p (drop₃-2 p≤q≤n) ω
                      (-₂ (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε X))
             p (psh .Face-coh))
           ≡ psh' .Face-coh
           → psh ≡ psh'
Presheaf-≡' psh psh' refl refl refl = refl

open import Axioms.FunExt
module Presheaf-FE
  (fe-axiom : FunExt-Axiom)
  where
  open FE fe-axiom
  open HSet-FE fe-axiom
  
  Presheaf-≡ : ∀ (psh psh' : Presheaf)
             → (F0≡ : ∀ n → psh .F0 n .Dom ≡ psh' .F0 n .Dom)
             → (∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
                          → (ε : arity) → (X : psh .F0 (1+ n) .Dom)
                          → transport (F0≡ n) (psh .Face n p p≤n ε X)
                          ≡ psh' .Face n p p≤n ε (transport (F0≡ (1+ n)) X))
             → psh ≡ psh'
  Presheaf-≡ psh psh' F0≡ Face≡ = Presheaf-≡' psh psh'
    (funExt λ n → HSet-≡ _ _ (F0≡ n))
    (funExt λ n → funExt λ p → funExt-impl (funExt λ p≤n →
    funExt λ ε → funExt λ X → I n p p≤n ε X))
    (funExt λ n → funExt λ p → funExt λ q → funExt-impl (
     funExt λ p≤q≤n → funExt λ ε → funExt λ ω →
     funExt λ X → psh' .F0 n .has-UIP _ _ _ _))
   where  
    I : ∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
      → (ε : arity)
      → (X : psh' .F0 (1+ n) .Dom)
      → subst (λ - → ∀ n p {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
           (funExt (λ n → HSet-≡ _ _ (F0≡ n)))
           (psh .Face) n p p≤n ε X
      ≡ psh' .Face n p p≤n ε X
    I n p {δ} p≤n ε X =
      subst (λ - → ∀ n p {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face) n p {δ} p≤n ε X
       ≡⟨ happly (happly (happly (happly-impl (happly
           (subst-application
              (λ - → ∀ n p {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
              (λ _ - → - n) (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n))))
            p) δ) p≤n) ε) X ⟩⁻¹
      subst (λ - → ∀ p {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n) p {δ} p≤n ε X
       ≡⟨ happly (happly (happly (happly-impl
           (subst-application
              (λ - → ∀ p {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
              {B₂ = λ - → ∀ {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom}
              (λ _ - → - p) (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n))))
            δ) p≤n) ε) X ⟩⁻¹
       subst (λ - → ∀ {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p) p≤n ε X
       ≡⟨ happly (happly (happly
            (subst-application
              (λ - → ∀ {δ} → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
              (λ _ - → - {δ}) (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n))))
            p≤n) ε) X  ⟩⁻¹
      subst (λ - → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p) p≤n ε X
       ≡⟨ happly (happly
            (subst-application (λ - → [ p ≤ n ][ δ ]₂ → arity → - (1+ n) .Dom → - n .Dom)
              (λ _ - → - p≤n) (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n))))
           ε) X  ⟩⁻¹
      subst (λ - → arity → - (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p p≤n) ε X
       ≡⟨ happly (subst-application (λ - → arity → - (1+ n) .Dom → - n .Dom) (λ _ - → - ε)
            (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))) X ⟩⁻¹
      subst (λ - → - (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p p≤n ε) X
       ≡⟨ happly (subst-dup (λ -₁ -₂ → -₁ (1+ n) .Dom → -₂ n .Dom)
             (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
             (psh .Face n p p≤n ε)) X ⟩
      subst (λ - → - (1+ n) .Dom → psh' .F0 n .Dom)
         (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
      (subst (λ - → psh .F0 (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p p≤n ε)) X
       ≡⟨ happly (funExt-subst (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)) (1+ n) _) _ ⟩
      subst (λ - → - .Dom → psh' .F0 n .Dom)
         (HSet-≡ (psh .F0 (1+ n)) (psh' .F0 (1+ n)) (F0≡ (1+ n)))
      (subst (λ - → psh .F0 (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p p≤n ε)) X
       ≡⟨ happly (HSet-≡-subst (psh .F0 (1+ n)) (psh' .F0 (1+ n)) (F0≡ (1+ n))) _ ⟩
      subst (λ - → - → psh' .F0 n .Dom)
         (F0≡ (1+ n))
      (subst (λ - → psh .F0 (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p p≤n ε)) X
       ≡⟨ happly (subst-fun-l (F0≡ (1+ n))
           (subst (λ - → psh .F0 (1+ n) .Dom → - n .Dom)
           (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
           (psh .Face n p p≤n ε))) X ⟩
      subst (λ - → psh .F0 (1+ n) .Dom → - n .Dom)
        (funExt (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)))
        (psh .Face n p p≤n ε) (transport (sym (F0≡ (1+ n))) X)
       ≡⟨ happly (funExt-subst (λ n → HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n)) n _) _ ⟩
      subst (λ - → psh .F0 (1+ n) .Dom → - .Dom)
        (HSet-≡ (psh .F0 n) (psh' .F0 n) (F0≡ n))
        (psh .Face n p p≤n ε) (transport (sym (F0≡ (1+ n))) X)
       ≡⟨ happly (HSet-≡-subst (psh .F0 n) (psh' .F0 n) (F0≡ n)) _ ⟩
      subst (λ - → psh .F0 (1+ n) .Dom → -) (F0≡ n)
        (psh .Face n p p≤n ε) (transport (sym (F0≡ (1+ n))) X)
       ≡⟨ happly (subst-fun-r (F0≡ n) (psh .Face n p p≤n ε)) (transport (sym (F0≡ (1+ n))) X) ⟩
      transport (F0≡ n) (psh .Face n p p≤n ε (transport (sym (F0≡ (1+ n))) X))
       ≡⟨ Face≡ n p p≤n ε _ ⟩
      psh' .Face n p p≤n ε (transport (F0≡ (1+ n)) (transport (sym (F0≡ (1+ n))) X))
       ≡⟨ cong (psh' .Face n p p≤n ε) (subst-sym-r (F0≡ (1+ n)) X) ⟩
      psh' .Face n p p≤n ε X ∎
     
open import Equiv
open import Axioms.Univalence

module Presheaf-UA
 (fe-axiom : FunExt-Axiom)
 (ua-axiom : Univalence-Axiom)
 where

  open UA ua-axiom
  open Presheaf-FE fe-axiom
  
  Presheaf-≃ : ∀ (psh psh' : Presheaf)
             → (F0≃ : ∀ n → psh .F0 n .Dom ≃ psh' .F0 n .Dom)
             → (∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
                          → (ε : arity) → (X : psh .F0 (1+ n) .Dom)
                          → F0≃ n .₁ (psh .Face n p p≤n ε X)
                          ≡ psh' .Face n p p≤n ε (F0≃ (1+ n) .₁ X))
             → psh ≡ psh'
  Presheaf-≃ psh psh' F0≃ Face≃ =
    Presheaf-≡ psh psh' (λ n → ua (F0≃ n)) I
    where
    I : ∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
      → (ε : arity) → (X : psh .F0 (1+ n) .Dom)
      → subst (λ - → -) (ua (F0≃ n)) (psh .Face n p p≤n ε X)
      ≡ psh' .Face n p p≤n ε (subst (λ - → -) (ua (F0≃ (1+ n))) X)
    I n p p≤n ε X =
      subst (λ - → -) (ua (F0≃ n)) (psh .Face n p p≤n ε X)
        ≡⟨ happly (ua-β (F0≃ n)) _ ⟩
       F0≃ n .₁ (psh .Face n p p≤n ε X)
        ≡⟨ Face≃ n p p≤n ε X ⟩
       psh' .Face n p p≤n ε (F0≃ (1+ n) .₁ X)
        ≡⟨ cong (psh' .Face n p p≤n ε) (happly (ua-β (F0≃ (1+ n))) X) ⟩⁻¹
       psh' .Face n p p≤n ε (subst (λ - → -) (ua (F0≃ (1+ n))) X) ∎ 

