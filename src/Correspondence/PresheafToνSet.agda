{-# OPTIONS --termination-depth=3 #-}

open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module Correspondence.PresheafToνSet
  (fe-axiom : FunExt-Axiom)
  (ua-axiom : Univalence-Axiom) 
  (arity : Type)
  where

open import Inequalities

open import HSet

open import Presheaf fe-axiom ua-axiom arity
open import νSet fe-axiom ua-axiom arity

open FE fe-axiom

Presheaf-νSet-< : ∀ m → (Psh-< : Presheaf-< m)
                → νSet-< m

Presheaf-νSet-= : ∀ m → (psh-< : Presheaf-< m)
                → νSet-= m (Presheaf-νSet-< m psh-<) 

Presheaf-frame : ∀ m →  (psh-< : Presheaf-< m)
               → ∀ p {δ} (p≤m :  [ p ≤ m ][ δ ]₂) 
               → psh-< .F0 .₁ .₂ .Dom
               → frame m p p≤m (Presheaf-νSet-< m psh-<) .Dom

Presheaf-νSet-< 0 psh-< = tt
Presheaf-νSet-< (1+ m) psh-< =
  (Presheaf-νSet-< m (psh₁ psh-<)) , Presheaf-νSet-= m (psh₁ psh-<)

Presheaf-νSet-= m psh-< d = 
  HΣ[ d' ∈ psh-< .F0 .₁ .₂ ]
  H≡ (fullframe (Presheaf-νSet-< m psh-<))
     d (Presheaf-frame m psh-< m (◆₂ m) d')

Presheaf-layer : ∀ m → (psh-< : Presheaf-< m)
               → ∀ p {δ} (p≤m :  [ 1+ p ≤ m ][ δ ]₂) 
               → (d : psh-< .F0 .₁ .₂ .Dom)
               → layer m p p≤m
                   (Presheaf-νSet-< m psh-<)
                   (Presheaf-frame m psh-< p (↓₂ p≤m) d) .Dom

Presheaf-painting : ∀ m → (psh-< : Presheaf-< m)
                  → ∀ p {δ} (p≤m :  [ p ≤ m ][ δ ]₂) 
                  → (d : psh-< .F0 .₁ .₂ .Dom)
                  → painting m p p≤m
                      (Presheaf-νSet-< m psh-<)
                      (Presheaf-νSet-= m psh-<)
                      (Presheaf-frame m psh-< p p≤m d) .Dom

Presheaf-restr-frame : ∀ m → (psh-< : Presheaf-< (1+ m))
                     → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃) ε
                     → (d : psh-< .F0 .₁ .₂ .Dom)
                     → Presheaf-frame m (psh₁ psh-<)
                         p (drop₃-2 p≤q≤m) (psh-< .Face .₁ .₂ q (drop₃-1 p≤q≤m) ε d)
                     ≡ restr-frame m p q p≤q≤m ε
                        (Presheaf-νSet-< (1+ m) psh-<)
                        (Presheaf-frame (1+ m) psh-< p (↑₂ drop₃-2 p≤q≤m) d)

Presheaf-restr-layer : ∀ m → (psh-< : Presheaf-< (1+ m))
                     → ∀ p q {δ} (p≤q≤m :  [ 1+ p ≤ 1+ q ≤ m ][ δ ]₃) ε
                     → (d : psh-< .F0 .₁ .₂ .Dom)
                     → subst (λ - → layer m p (drop₃-2 p≤q≤m)
                         (Presheaf-νSet-< m (psh₁ psh-<))
                         - .Dom)
                       (Presheaf-restr-frame m psh-< p (1+ q) (↓₃ p≤q≤m) ε d)
                       (Presheaf-layer m (psh₁ psh-<) p (drop₃-2 p≤q≤m) (psh-< .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
                     ≡ restr-layer m p q p≤q≤m ε
                         (Presheaf-νSet-< (1+ m) psh-<)
                         (Presheaf-frame (1+ m) psh-< p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)
                         (Presheaf-layer (1+ m) psh-< p (↑₂ drop₃-2 p≤q≤m) d) 

Presheaf-restr-painting : ∀ m → (psh-< : Presheaf-< (1+ m))
                        → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃) ε
                        → (d : psh-< .F0 .₁ .₂ .Dom)
                        → subst (λ - → painting m p (drop₃-2 p≤q≤m)
                            (Presheaf-νSet-< m (psh₁ psh-<))
                            (Presheaf-νSet-= m (psh₁ psh-<))
                            - .Dom)
                          (Presheaf-restr-frame m psh-< p q p≤q≤m ε d)
                          (Presheaf-painting m (psh₁ psh-<) p (drop₃-2 p≤q≤m)
                            (psh-< .Face .₁ .₂ q (drop₃-1 p≤q≤m) ε d))
                        ≡ restr-painting m p q p≤q≤m ε
                            (Presheaf-νSet-< (1+ m) psh-<)
                            (Presheaf-νSet-= (1+ m) psh-<)
                            (Presheaf-frame (1+ m) psh-< p (↑₂ drop₃-2 p≤q≤m) d )
                            (Presheaf-painting (1+ m) psh-< p (↑₂ drop₃-2 p≤q≤m) d) 
  
Presheaf-frame m psh-< zero   p≤m d = tt
Presheaf-frame m psh-< (1+ p) p≤m d =
  Presheaf-frame m psh-< p (↓₂ p≤m) d ,
  Presheaf-layer m psh-< p p≤m d

Presheaf-layer (1+ m) psh-< p p≤m d ε =
  subst (λ - → painting m p (⇓₂ p≤m)
                 (Presheaf-νSet-< m (psh₁ psh-<))
                 (Presheaf-νSet-= m (psh₁ psh-<))
                 - .Dom)
    (Presheaf-restr-frame m psh-< p p (◆₃ ⇓₂ p≤m) ε d)
    (Presheaf-painting m (psh₁ psh-<) p (⇓₂ p≤m) (psh-< .Face .₁ .₂ p (⇓₂ p≤m) ε d))


Presheaf-painting m psh p {zero} (ineq₂ Hpn) d with recover-nat-eq p m Hpn
... | refl = d , refl
Presheaf-painting m psh p {1+ δ} (ineq₂ Hpn) d =
  Presheaf-layer m psh p (ineq₂ _) d ,
  Presheaf-painting m psh (1+ p) {δ} (ineq₂ Hpn) d

Presheaf-restr-frame m psh zero q p≤q≤m ε d = refl
Presheaf-restr-frame m psh (1+ p) (1+ q) p≤q≤m ε d =
  Σ-≡→≡ ( Presheaf-restr-frame m psh p (1+ q) (↓₃ p≤q≤m) ε d
        , Presheaf-restr-layer m psh p q p≤q≤m ε d)

Presheaf-restr-layer (1+ m) psh p q p≤q≤m ε d = funExt λ ω →
  subst (λ - → layer (1+ m) p (ineq₂ _)
       (Presheaf-νSet-< (1+ m) (psh₁ psh)) - .Dom)
    (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d)
    (Presheaf-layer (1+ m) (psh₁ psh) p (drop₃-2 p≤q≤m) (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) ω
   ≡⟨ subst-application
        (λ - → layer (1+ m) p (ineq₂ _) (Presheaf-νSet-< (1+ m) (psh₁ psh)) - .Dom)
        (λ -₁ -₂ → -₂ ω)
        (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d) ⟩⁻¹
  subst (λ - → painting-m (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (psh₁ psh)) -))
    (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d) (
  subst painting-m
    (Presheaf-restr-frame m (psh₁ psh) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    (Presheaf-painting m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m)
      (psh .Face .₁ .₁ .₂ p (⇓₂ drop₃-2 p≤q≤m) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))))
   ≡⟨ subst-∘ (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d) _ ⟩
  subst painting-m
    (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (psh₁ psh)))
      (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d)) (
  subst painting-m
    (Presheaf-restr-frame m (psh₁ psh) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    (Presheaf-painting m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m)
      (psh .Face .₁ .₁ .₂ p (⇓₂ drop₃-2 p≤q≤m) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))))
   ≡⟨ cong (λ - →
        subst painting-m
          (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (psh₁ psh)))
            (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d)) (
        subst painting-m
          (Presheaf-restr-frame m (psh₁ psh) p p
            (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) -))
      (dcong (Presheaf-painting m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m)) (psh .Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d)) ⟩⁻¹
  subst painting-m
    (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (psh₁ psh)))
      (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d)) (
  subst painting-m
    (Presheaf-restr-frame m (psh₁ psh) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) (
  subst (λ - → painting-m (Presheaf-frame m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m) -))
    (psh .Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d)
    (Presheaf-painting m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m)
      (psh .Face .₁ .₁ .₂ q (⇓₂ drop₃-1 p≤q≤m) ε (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))))
   ≡⟨ cong (λ - →
        subst painting-m
          (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (psh₁ psh)))
            (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d)) (
        subst painting-m
          (Presheaf-restr-frame m (psh₁ psh) p p
            (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) -))
        (subst-∘ (psh .Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d) _) ⟩
  subst painting-m
    (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (psh₁ psh)))
      (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d)) (
  subst painting-m
    (Presheaf-restr-frame m (psh₁ psh) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) (
  subst painting-m
    (cong (Presheaf-frame m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m))
      (psh .Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d))
    (Presheaf-painting m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m)
      (psh .Face .₁ .₁ .₂ q (⇓₂ drop₃-1 p≤q≤m) ε (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))))  
   ≡⟨ coh₂ {A = frame m p (⇓₂ drop₃-2 p≤q≤m) (Presheaf-νSet-< m (psh₁ (psh₁ psh)))}
        (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (psh₁ psh)))
          (Presheaf-restr-frame (1+ m) psh p (1+ q) (↓₃ p≤q≤m) ε d))
        (Presheaf-restr-frame m (psh₁ psh) p p
          (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
        (cong (Presheaf-frame m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m))
          (psh .Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d))
        (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
          (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d))
        (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (psh₁ psh)))
          (Presheaf-restr-frame (1+ m) psh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d))
        (Presheaf-restr-frame m (psh₁ psh) p q (⇓₃ p≤q≤m) ε
          (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)) ⟩
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
      (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
  subst painting-m
    (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (psh₁ psh)))
      (Presheaf-restr-frame (1+ m) psh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)) (
  subst painting-m
    (Presheaf-restr-frame m (psh₁ psh) p q (⇓₃ p≤q≤m) ε
      (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))
    (Presheaf-painting m (psh₁ (psh₁ psh)) p (⇓₂ drop₃-2 p≤q≤m)
      (psh .Face .₁ .₁ .₂ q (⇓₂ drop₃-1 p≤q≤m) ε (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))))
   ≡⟨ cong (λ - →
        subst painting-m
          (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
            (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
        subst painting-m
          (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (psh₁ psh)))
            (Presheaf-restr-frame (1+ m) psh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)) -))
        (Presheaf-restr-painting m (psh₁ psh) p q (⇓₃ p≤q≤m) ε
          (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)) ⟩
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
      (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
  subst painting-m
    (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (psh₁ psh)))
       (Presheaf-restr-frame (1+ m) psh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d))
    (restr-painting m p q (⇓₃ p≤q≤m) ε
        (Presheaf-νSet-< (1+ m) (psh₁ psh))
        (Presheaf-νSet-= (1+ m) (psh₁ psh))
        (Presheaf-frame (1+ m) (psh₁ psh) p (↑₂ drop₃-2 (⇓₃ p≤q≤m))
           (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))
        (Presheaf-painting (1+ m) (psh₁ psh) p (↓₂ drop₃-2 p≤q≤m) (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))) 
   ≡⟨ cong (subst painting-m
             (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
               (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)))
           (subst-∘ (Presheaf-restr-frame (1+ m) psh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d) _) ⟩⁻¹
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
      (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
  subst (λ - → painting-m (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (psh₁ psh)) -))
    (Presheaf-restr-frame (1+ m) psh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)
    (restr-painting m p q (⇓₃ p≤q≤m) ε
        (Presheaf-νSet-< (1+ m) (psh₁ psh))
        (Presheaf-νSet-= (1+ m) (psh₁ psh))
        (Presheaf-frame (1+ m) (psh₁ psh) p (↑₂ drop₃-2 (⇓₃ p≤q≤m))
           (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))
        (Presheaf-painting (1+ m) (psh₁ psh) p (↓₂ drop₃-2 p≤q≤m) (psh .Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))))
   ≡⟨ cong (subst painting-m
              (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
                (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)))
            (subst-application (λ - → painting (1+ m) p (↓₂ drop₃-2 p≤q≤m)
                 (Presheaf-νSet-< (1+ m) (psh₁ psh))
                 (Presheaf-νSet-= (1+ m) (psh₁ psh))
                 - .Dom)
                 (restr-painting m p q (⇓₃ p≤q≤m) ε
                    (Presheaf-νSet-< (1+ m) (psh₁ psh))
                    (Presheaf-νSet-= (1+ m) (psh₁ psh)))
                 (Presheaf-restr-frame (1+ m) psh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)) ⟩
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) psh)
      (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d))
    (restr-painting m p q (⇓₃ p≤q≤m) ε
      (Presheaf-νSet-< (1+ m) (psh₁ psh))
      (Presheaf-νSet-= (1+ m) (psh₁ psh))
      (restr-frame (1+ m) p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω
        (Presheaf-νSet-< (2+ m) psh)
        (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d))
      (Presheaf-layer (2+ m) psh p (↑₂ drop₃-2 p≤q≤m) d ω))
   ≡⟨⟩
  restr-layer (1+ m) p q p≤q≤m ε (Presheaf-νSet-< (2+ m) psh)
    (Presheaf-frame (2+ m) psh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)
    (Presheaf-layer (2+ m) psh p (↑₂ drop₃-2 p≤q≤m) d) ω ∎
  where
  painting-m : frame m p (⇓₂ drop₃-2 p≤q≤m) (Presheaf-νSet-< m (psh₁ (psh₁ psh))) .Dom → Type
  painting-m d =
    painting m p (⇓₂ drop₃-2 p≤q≤m)
      (Presheaf-νSet-< m (psh₁ (psh₁ psh)))
      (Presheaf-νSet-= m (psh₁ (psh₁ psh)))
      d .Dom

Presheaf-restr-painting m psh p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) ε d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
Presheaf-restr-painting m psh p (1+ q) {1+ δ} p≤q≤m@(ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) ε d =
  subst painting-m
    (Presheaf-restr-frame m psh p (1+ q) p≤q≤m ε d)
    (Presheaf-painting m (psh₁ psh) p (drop₃-2 p≤q≤m)
       (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    ≡⟨ subst-Σ (Presheaf-restr-frame m psh p (1+ q) p≤q≤m ε d) ⟩
  subst (λ - → layer m p (drop₃-2 1+p≤q≤m) (Presheaf-νSet-< m (psh₁ psh)) - .Dom)
    (Presheaf-restr-frame m psh p (1+ q) p≤q≤m ε d)
    (Presheaf-layer m (psh₁ psh) p (drop₃-2 1+p≤q≤m)
      (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) ,
  subst painting-m'
     (Σ-≡→≡ (Presheaf-restr-frame m psh p (1+ q) p≤q≤m ε d , refl))
     (Presheaf-painting m (psh₁ psh) (1+ p) (drop₃-2 1+p≤q≤m)
       (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    ≡⟨ Σ-≡→≡ ( Presheaf-restr-layer m psh p q 1+p≤q≤m ε d
             , subst-Σ' (Presheaf-restr-frame m psh p (1+ q) p≤q≤m ε d)
                         (Presheaf-restr-layer m psh p q 1+p≤q≤m ε d)) ⟩
  restr-layer m p q 1+p≤q≤m ε
    (Presheaf-νSet-< (1+ m) psh)
    (Presheaf-frame (1+ m) psh p (↑₂ drop₃-2 p≤q≤m) d)
    (Presheaf-layer (1+ m) psh p (⇑₂ drop₃-2 p≤q≤m) d) ,
  subst painting-m'
    (Presheaf-restr-frame m psh (1+ p) (1+ q) 1+p≤q≤m ε d)
    (Presheaf-painting m (psh₁ psh) (1+ p) (drop₃-2 1+p≤q≤m)
       (psh .Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) 
    ≡⟨ Σ-≡→≡ ( refl , Presheaf-restr-painting m psh (1+ p) (1+ q) 1+p≤q≤m ε d) ⟩
  restr-painting m p (1+ q) p≤q≤m ε
    (Presheaf-νSet-< (1+ m) psh)
    (Presheaf-νSet-= (1+ m) psh)
    (Presheaf-frame (1+ m) psh p
      (↑₂ drop₃-2 p≤q≤m) d)
    (Presheaf-painting (1+ m) psh p (↑₂ drop₃-2 p≤q≤m) d) ∎
  where
  1+p≤q≤m : [ 1+ p ≤ 1+ q ≤ m ][ δ ]₃
  1+p≤q≤m = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn
  
  painting-m : frame m p (drop₃-2 p≤q≤m) (Presheaf-νSet-< m (psh₁ psh)) .Dom → Type
  painting-m d =
    painting m p (drop₃-2 p≤q≤m)
      (Presheaf-νSet-< m (psh₁ psh))
      (Presheaf-νSet-= m (psh₁ psh))
      d .Dom

  painting-m' : frame m (1+ p) (drop₃-2 1+p≤q≤m) (Presheaf-νSet-< m (psh₁ psh)) .Dom → Type
  painting-m' d =
    painting m (1+ p) (drop₃-2 1+p≤q≤m)
      (Presheaf-νSet-< m (psh₁ psh))
      (Presheaf-νSet-= m (psh₁ psh))
      d .Dom

Presheaf-next : ∀ m
              → (zipper : Presheaf-zipper m)
              → νSet-> m (Presheaf-νSet-< m (psh→psh-< zipper))
Presheaf-next m zipper .this = Presheaf-νSet-= m (psh→psh-< zipper)
Presheaf-next m zipper .next = Presheaf-next (1+ m) (bump-zipper m zipper)

f : Presheaf → νSet
f psh = Presheaf-next 0 (psh→zipper psh)
