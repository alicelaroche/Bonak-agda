{-# OPTIONS --termination-depth=3 #-}

open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module Correspondence
  (fe-axiom : FunExt-Axiom)
  (ua-axiom : Univalence-Axiom) 
  (arity : Type)
  where

open import Inequalities
open import Equiv

open import HSet
open HSet-FE fe-axiom

open import Presheaf fe-axiom ua-axiom arity
open import νSet fe-axiom ua-axiom arity

open FE fe-axiom

record RestrInfo (n : ℕ) : Type where
  constructor info
  field
    restr-p : ℕ
    restr-δ : ℕ
    restr-ε : arity
    restr-p≤n : [ restr-p ≤ n ][ restr-δ ]₂
open RestrInfo public

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

Presheaf-getFrame : ∀ m → (psh : Presheaf-< m)
                  → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃)
                  → (d : psh .F0 .₁ .₂ .Dom)
                  → getFrame m p q p≤q≤m _ (Presheaf-frame m psh q (drop₃-1 p≤q≤m) d)
                  ≡ Presheaf-frame m psh p (drop₃-2 p≤q≤m) d
Presheaf-getFrame m psh p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
Presheaf-getFrame m psh p (1+ q) {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) d =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in 
  cong ₁ (Presheaf-getFrame m psh (1+ p) (1+ q) {δ} 1+p≤q≤n d)

Presheaf-getPainting : ∀ m → (psh : Presheaf-< m)
                     → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃)
                     → (d : psh .F0 .₁ .₂ .Dom)
                     → getPainting m p q p≤q≤m
                         (Presheaf-νSet-< m psh)
                         (Presheaf-νSet-= m psh)
                         (Presheaf-frame m psh p (drop₃-2 p≤q≤m) d)
                         (Presheaf-painting m psh p (drop₃-2 p≤q≤m) d)
                     ≡ ( Presheaf-frame m psh q (drop₃-1 p≤q≤m) d
                       , Presheaf-painting m psh q (drop₃-1 p≤q≤m) d)
Presheaf-getPainting m psh p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
Presheaf-getPainting m psh p q {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) d =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  Presheaf-getPainting m psh (1+ p) q {δ} 1+p≤q≤n d

Presheaf-νFace : ∀ m → (psh : Presheaf-< (1+ m))
               → ∀ p {δ} (p≤m :  [ p ≤ m ][ δ ]₂) ε
               → (d : psh .F0 .₁ .₂ .Dom)
               → νFace m p p≤m ε _ (Presheaf-frame (1+ m) psh (1+ m) (◆₂ (1+ m)) d)
               ≡ ( Presheaf-frame m (psh₁ psh) m (◆₂ m) (psh .Face .₁ .₂ p p≤m ε d)
                 , psh .Face .₁ .₂ p p≤m ε d , refl)
Presheaf-νFace m psh p p≤m ε d =
  νFace m p p≤m ε _ (Presheaf-frame (1+ m) psh (1+ m) (◆₂ (1+ m)) d)
    ≡⟨⟩
  getPainting m p m (◆₃' p≤m) _ _ _
    (getFrame (1+ m) (1+ p) (1+ m) (⇑₃ ◆₃' p≤m) _ (Presheaf-frame (1+ m) psh (1+ m) (◆₂ (1+ m)) d) .₂ ε)
    ≡⟨ cong (λ - → getPainting m p m (◆₃' p≤m) _ _ _ (- .₂ ε))
            (Presheaf-getFrame (1+ m) psh (1+ p) (1+ m) (⇑₃ ◆₃' p≤m) d) ⟩
  getPainting m p m (◆₃' p≤m) _ _ _
    ((Presheaf-frame (1+ m) psh (1+ p) (⇑₂ p≤m) d) .₂ ε)
    ≡⟨  subst-application (λ - → painting m p (⇓₂ (⇑₂ p≤m))
            (Presheaf-νSet-< m (psh₁ psh))
            (Presheaf-νSet-= m (psh₁ psh)) - .Dom)
            (λ - → getPainting m p m (◆₃' p≤m) _ _ -)
            (Presheaf-restr-frame m psh p p (◆₃ (⇓₂ (⇑₂ p≤m))) ε d) ⟩⁻¹
  subst (λ _ → _)
   (Presheaf-restr-frame m psh p p (◆₃ p≤m) ε d)
   (getPainting m p m (◆₃' p≤m) _ _
    (Presheaf-frame m (psh₁ psh) p p≤m (psh .Face .₁ .₂ p (⇓₂ (⇑₂ p≤m)) ε d))
    (Presheaf-painting m (psh₁ psh) p p≤m
      (psh .Face .₁ .₂ p p≤m ε d)))
    ≡⟨ subst-const (Presheaf-restr-frame m psh p p (◆₃ p≤m) ε d) _ ⟩ 
  getPainting m p m (◆₃' p≤m) _ _
    (Presheaf-frame m (psh₁ psh) p p≤m (psh .Face .₁ .₂ p (⇓₂ (⇑₂ p≤m)) ε d))
    (Presheaf-painting m (psh₁ psh) p p≤m
      (psh .Face .₁ .₂ p p≤m ε d))
    ≡⟨ Presheaf-getPainting m (psh₁ psh) p m (◆₃' p≤m) (psh .Face .₁ .₂ p p≤m ε d) ⟩
  ( Presheaf-frame m (psh₁ psh) m (◆₂ m) (psh .Face .₁ .₂ p p≤m ε d)
  , psh .Face .₁ .₂ p p≤m ε d , refl) ∎


νSet-F0-< : ∀ m → νSet-< m → F0-< m 
νSet-F0-< zero D = tt
νSet-F0-< (1+ m) (D , E) = (νSet-F0-< m D) , (TotalSpace D E)

νSet-Face-< : ∀ m → (D : νSet-< (1+ m))
            → Face-< m (νSet-F0-< (1+ m) D)
νSet-Face-< zero D = tt
νSet-Face-< (1+ m) (D , E) = νSet-Face-< m D ,  λ p p≤n ε d → νFace m p p≤n ε D (d .₁)

νSet-Coh-< : ∀ m → (D : νSet-< (2+ m))
         → Coh-< m (νSet-F0-< (2+ m) D) (νSet-Face-< (1+ m) D)
νSet-Coh-< zero   D = tt
νSet-Coh-< (1+ m) ((D , E) , E') = νSet-Coh-< m (D , E) , λ p q p≤q≤m ε ω d → νFace-coh m p q p≤q≤m ε ω (D , E) (d .₁)

νSet-psh-< : ∀ {m} → (D : νSet-< (2+ m)) → Presheaf-< m
νSet-psh-< D .F0 = νSet-F0-< _ D
νSet-psh-< D .Face = νSet-Face-< _ D
νSet-psh-< D .Coh = νSet-Coh-< _ D

νSet-F0-≥ : ∀ m → (D : νSet-< m) → νSet-> m D → ℕ → HSet
νSet-F0-≥ m D νSet 0      = TotalSpace D (νSet .this)
νSet-F0-≥ m D νSet (1+ n) = νSet-F0-≥ (1+ m) (D , νSet .this) (νSet .next) n

νSet-Face-> : ∀ m → (D : νSet-< m) (νSet : νSet-> m D)
            → ∀ n p {δ}
            → [ p ≤ n + m ][ δ ]₂ → arity
            → νSet-F0-≥ m D νSet (1+ n) .Dom
            → νSet-F0-≥ m D νSet n .Dom
νSet-Face-> m D νSet 0 p p≤m ε d = νFace m p p≤m ε (D , νSet .this) (d .₁)
νSet-Face-> m D νSet (1+ n) = νSet-Face-> (1+ m) (D , νSet .this) (νSet .next) n

νSet-Coh-> : ∀ m → (D : νSet-< m) (νSet : νSet-> m D)
            → ∀ n p q {δ}
            → (p≤q≤n : [ p ≤ q ≤ n + m ][ δ ]₃) 
            → (ε ω : arity)
            → (d : νSet-F0-≥ m D νSet (2+ n) .Dom)
            → νSet-Face-> m D νSet n q (drop₃-1 p≤q≤n) ε
               (νSet-Face-> m D νSet (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω d)
            ≡ νSet-Face-> m D νSet n p (drop₃-2 p≤q≤n) ω
               (νSet-Face-> m D νSet (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε d)
νSet-Coh-> m D νSet zero p q p≤q≤m ε ω d =  νFace-coh m p q p≤q≤m ε ω (_ , νSet .next .this) (d .₁)
νSet-Coh-> m D νSet (1+ n) = νSet-Coh-> (1+ m) (D , νSet .this) (νSet .next) n



g : νSet → Presheaf
g νSet .F0 = νSet-F0-≥ 0 tt νSet
g νSet .Face = νSet-Face-> 0 tt νSet
g νSet .Face-coh = νSet-Coh-> 0 tt νSet

νSet→zipper : ∀ m (D : νSet-< m) (νSet : νSet-> m D) → Presheaf-zipper m
νSet→zipper m D νSet .|F0-<| = νSet-F0-< m D
νSet→zipper m D νSet .|F0-≥| = νSet-F0-≥ m D νSet
νSet→zipper m D νSet .|Face-<| = νSet-Face-< m (D , νSet .this)
νSet→zipper m D νSet .|Face-≥| = νSet-Face-> m D νSet
νSet→zipper m D νSet .|Coh-<| = νSet-Coh-< m ((D , νSet .this) , νSet .next .this)
νSet→zipper m D νSet .|Coh-≥| = νSet-Coh-> m D νSet


f∘g-νSet-< : ∀ m → (D : νSet-< (2+ m))
           → νSet-<-≃ (Presheaf-νSet-< m (νSet-psh-< D)) (D .₁ .₁)

f∘g-νSetₙ : ∀ m
          → (D : νSet-< (2+ m))
          → (d : fullframe (D .₁ .₁) .Dom)
          → (Σ[ d' ∈ TotalSpace (D .₁ .₁) (D .₁ .₂) .Dom ]
          ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
          ≡ Presheaf-frame m (νSet-psh-< D) m (◆₂ m) d'))
          ≃ D .₁ .₂ d .Dom

f∘g-frame-≡ : ∀ m
            → (D : νSet-< (2+ m))
            → (d : fullframe (D .₁ .₁) .Dom)
            → (c : D .₁ .₂ d .Dom)
            → subst (λ - → fullframe - .Dom)
                (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
            ≡ Presheaf-frame m (νSet-psh-< D) m (◆₂ m) (d , c)

f∘g-νSet-< 0 D = ≃[]
f∘g-νSet-< (1+ m) D = f∘g-νSet-< m (D .₁) ≃∷ f∘g-νSetₙ m (D .₁)

f∘g-νSetₙ m D d = f' , (g' , g'∘f'∼id) , (g' , f'∘g'∼id)
 where

 f' : Σ[ d' ∈ TotalSpace (D .₁ .₁) (D .₁ .₂) .Dom ]
    ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
    ≡ Presheaf-frame m (νSet-psh-< D) m (◆₂ m) d')
    → D .₁ .₂ d .Dom
 f' ((d' , c) , eq) = subst (λ - → D .₁ .₂ - .Dom) (sym (subst-inj _ (eq ∙ (sym (f∘g-frame-≡ m D d' c))))) c

 g' : D .₁ .₂ d .Dom
    → Σ[ d' ∈ TotalSpace (D .₁ .₁) (D .₁ .₂) .Dom ]
    ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
    ≡ Presheaf-frame m (νSet-psh-< D) m (◆₂ m) d')
 g' c = (d , c) , f∘g-frame-≡ m D d c
 
 g'∘f'∼id : ∀ c → g' (f' c) ≡ c
 g'∘f'∼id ((d' , c) , coh) = Σ-≡→≡ (Σ-≡→≡ (
    subst-inj _ (coh ∙ (sym (f∘g-frame-≡ m D d' c))) ,
    subst-sym-r (subst-inj (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) (coh ∙ (sym (f∘g-frame-≡ m D d' c)))) c) ,
    fullframe (Presheaf-νSet-< m (νSet-psh-< D))
      .has-UIP _ _ _ coh)

 f'∘g'∼id : ∀ c → f' (g' c) ≡ c
 f'∘g'∼id c = cong (λ -₁ → subst (λ - → D .₁ .₂ - .Dom) -₁ c)
              ( cong (sym ∘ (subst-inj (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))))) (trans-sym-r (g' c .₂))
              ∙ J (λ _ eq → sym (subst-inj eq refl) ≡ refl) refl (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))))

f∘g-frame-≡ zero D d c = refl
f∘g-frame-≡ (1+ m) D d c = νFace-≡ m _ _ _ λ p p≤n ε →
   νFace m p p≤n ε
    (Presheaf-νSet-< (1+ m) (νSet-psh-< D))
    (subst (λ - → fullframe - .Dom)
     (sym (νSet-<-≃→≡ (f∘g-νSet-< (1+ m) D))) d)
    ≡⟨ νFace-νSet-<-≃ m _ _ _ _ (f∘g-νSet-< m (D .₁)) (f∘g-νSetₙ m (D .₁)) d p p≤n ε  ⟩
  subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m (D .₁)))) (νFace m p p≤n ε _ d .₁) ,
  νFace m p p≤n ε (D .₁ .₁) d ,
  f∘g-frame-≡ m (D .₁) (νFace m p p≤n ε (D .₁ .₁) d .₁) (νFace m p p≤n ε (D .₁ .₁) d .₂)
    ≡⟨  J' (λ a eq → (a , νFace m p p≤n ε (D .₁ .₁) d , eq)
                  ≡ (Presheaf-frame m (νSet-psh-< (D .₁)) m (◆₂ m)
                      (νFace m p p≤n ε (D .₁ .₁) d) ,
                    νFace m p p≤n ε (D .₁ .₁) d ,
                    refl))
           refl
           (f∘g-frame-≡ m (D .₁) (νFace m p p≤n ε (D .₁ .₁) d .₁) (νFace m p p≤n ε (D .₁ .₁) d .₂))  ⟩
  Presheaf-frame m (νSet-psh-< (D .₁)) m (◆₂ m)
    (νFace m p p≤n ε (D .₁ .₁) d) ,
  νFace m p p≤n ε (D .₁ .₁) d ,
  refl
    ≡⟨ Presheaf-νFace m (νSet-psh-< D) p p≤n ε (d , c) ⟩⁻¹
  νFace m p p≤n ε
    (Presheaf-νSet-< (1+ m) (νSet-psh-< D))
    (Presheaf-frame (1+ m) (νSet-psh-< D) (1+ m) (◆₂ (1+ m)) (d , c)) ∎

f∘g-νSet-> : ∀ m → (D : νSet-< m) (νSet : νSet-> m D)
           → νSet->-≃ (f∘g-νSet-< m ((D , νSet .this) , νSet .next .this))
              (Presheaf-next m (νSet→zipper m D νSet))
              νSet
f∘g-νSet-> m D νSet .this-≃ = f∘g-νSetₙ m ((D , νSet .this) , νSet .next .this)
f∘g-νSet-> m D νSet .next-≃ = f∘g-νSet-> (1+ m) (D , νSet .this) (νSet .next)

g∘f-F0 : ∀ m → (zipper : Presheaf-zipper m)
       → ∀ n
       → νSet-F0-≥ m
           (Presheaf-νSet-< m (psh→psh-< zipper))
           (Presheaf-next m zipper)
           n .Dom
       ≃ zipper .|F0-≥| n .Dom
g∘f-F0 m zipper (1+ n) = g∘f-F0 (1+ m) (bump-zipper m zipper) n
g∘f-F0 m zipper 0 = f' , (g' , g'∘f'∼id ) , (g' , f'∘g'∼id)
  where
  f' : TotalSpace
        (Presheaf-νSet-< m (psh→psh-< zipper))
        (Presheaf-νSet-= m (psh→psh-< zipper))
        .Dom
     → zipper .|F0-≥| 0 .Dom
  f' (d , (c , eq)) = c

  g' : zipper .|F0-≥| 0 .Dom
     → TotalSpace
        (Presheaf-νSet-< m (psh→psh-< zipper))
        (Presheaf-νSet-= m (psh→psh-< zipper))
        .Dom
  g' d = _ , (d , refl)

  g'∘f'∼id : ∀ c → g' (f' c) ≡ c
  g'∘f'∼id (d , c , refl) = refl

  f'∘g'∼id : ∀ c → f' (g' c) ≡ c
  f'∘g'∼id c = refl

g∘f-Face : ∀ m → (zipper : Presheaf-zipper m)
         → ∀ n p {δ} (p≤n : [ p ≤ n + m ][ δ ]₂) ε
         → (d : νSet-F0-≥ (1+ m)
                  (Presheaf-νSet-< (1+ m) (psh→psh-< (bump-zipper m zipper)))
                  (Presheaf-next (1+ m) (bump-zipper m zipper))
                  n .Dom)
         → g∘f-F0 m zipper n .₁
           (νSet-Face-> m
              (Presheaf-νSet-< m (psh→psh-< zipper))
              (Presheaf-next m zipper)
              n p p≤n ε d)
         ≡ zipper .|Face-≥| n p p≤n ε
            (g∘f-F0 m zipper (1+ n) .₁ d) 
g∘f-Face m zipper (1+ n) = g∘f-Face (1+ m) (bump-zipper m zipper) n
g∘f-Face m zipper zero p p≤n ε (d , (c , eq)) =
  (νFace m p p≤n ε (Presheaf-νSet-< (1+ m) (psh→psh-< (bump-zipper m zipper)))
    d) .₂ .₁
    ≡⟨ cong (λ - → (νFace m p p≤n ε _ -) .₂ .₁) eq ⟩
  (νFace m p p≤n ε (Presheaf-νSet-< (1+ m) (psh→psh-< (bump-zipper m zipper)))
    (Presheaf-frame (1+ m) (psh→psh-< (bump-zipper m zipper)) (1+ m) (◆₂ (1+ m)) c)) .₂ .₁
    ≡⟨ cong (λ - → - .₂ .₁) (Presheaf-νFace m (psh→psh-< (bump-zipper m zipper)) p p≤n ε c) ⟩
  zipper .|Face-≥| zero p p≤n ε c ∎

f∘g : ∀ νSet → νSet-≃ (f (g νSet)) νSet 
f∘g νSet = f∘g-νSet-> 0 tt νSet

g∘f : ∀ psh → g (f psh) ≡ psh
g∘f psh = Presheaf-≃ (g (f psh)) psh
           (g∘f-F0 0 (psh→zipper psh))
           (g∘f-Face 0 (psh→zipper psh))
