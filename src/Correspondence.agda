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

open import Category arity
open import νSet fe-axiom ua-axiom arity

open FE fe-axiom
open UA ua-axiom

open Presheaf-UA fe-axiom ua-axiom

record RestrInfo (n : ℕ) : Type where
  constructor info
  field
    restr-p : ℕ
    restr-δ : ℕ
    restr-ε : arity
    restr-p≤n : [ restr-p ≤ n ][ restr-δ ]₂
open RestrInfo public

F0-< : (m : ℕ) → Type₁
F0-< zero   = ⊤
F0-< (1+ m) = F0-< m × HSet

Face-≤ : (m : ℕ) → F0-< (1+ m) → Type₁
Face-≤ zero   F0s = ⊤
Face-≤ (1+ m) ((F0s , F0) , F0')  =
  Face-≤ m (F0s , F0) × (∀ p {δ} → [ p ≤ m ][ δ ]₂ → arity → F0' .Dom → F0 .Dom)

Coh-≤ : (m : ℕ) → (F0s : F0-< (2+ m)) → Face-≤ (1+ m) F0s → Type₁
Coh-≤ zero F0s faces = ⊤
Coh-≤ (1+ m) F0s ((faces , face) , face') =
  Coh-≤ m (F0s .₁) (faces , face) ×
  (∀ p q {δ} (p≤q≤m : [ p ≤ q ≤ m ][ δ ]₃) ε ω d
  → face q (drop₃-1 p≤q≤m) ε (face' p (↑₂ drop₃-2 p≤q≤m) ω d)
  ≡ face p (drop₃-2 p≤q≤m) ω (face' (1+ q) (⇑₂ drop₃-1 p≤q≤m) ε d))

record F0-≥ (m : ℕ) : Type₁ where
  coinductive
  field
   there : HSet
   after : F0-≥ (1+ m)
open F0-≥

record Face-> (m : ℕ) (F0s : F0-≥ m) : Type₁ where
  coinductive
  field
   there' : ∀ p {δ}
          → [ p ≤ m ][ δ ]₂ → arity
          → F0s .after .there .Dom
          → F0s .there .Dom
   after' : Face-> (1+ m) (F0s .after)
open Face->

record Presheaf-zipper (m : ℕ) : Type₁ where
  field
   |F0-<| : F0-< m
   |F0-≥| : ∀ n → HSet
   |Face-≤| : Face-≤ m (|F0-<| , |F0-≥| 0)
   |Face->| : ∀ n p {δ}
            → [ p ≤ n + m ][ δ ]₂ → arity
            → |F0-≥| (1+ n) .Dom
            → |F0-≥| n .Dom
   |Coh-≤| : Coh-≤ m ((|F0-<| , |F0-≥| 0) , |F0-≥| 1) (|Face-≤| , |Face->| 0)
   |Coh->| : ∀ n p q {δ}
           → (p≤q≤m : [ p ≤ q ≤ n + m ][ δ ]₃)
           → (ε ω : arity)
           → (d : |F0-≥| (2+ n) .Dom)
           → |Face->| n q (drop₃-1 p≤q≤m) ε (|Face->| (1+ n) p (↑₂ drop₃-2 p≤q≤m) ω d)
           ≡ |Face->| n p (drop₃-2 p≤q≤m) ω (|Face->| (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤m) ε d)
open Presheaf-zipper

bump-zipper : ∀ m → Presheaf-zipper m → Presheaf-zipper (1+ m)
bump-zipper m zipper .|F0-<| = zipper .|F0-<| , zipper .|F0-≥| 0
bump-zipper m zipper .|F0-≥| = zipper .|F0-≥| ∘ suc
bump-zipper m zipper .|Face-≤| = zipper .|Face-≤| , zipper .|Face->| 0
bump-zipper m zipper .|Face->| = zipper .|Face->| ∘ suc
bump-zipper m zipper .|Coh-≤| = zipper .|Coh-≤| , (λ p q {δ} → zipper .|Coh->| 0 p q)
bump-zipper m zipper .|Coh->| = zipper .|Coh->| ∘ suc

psh→zipper : Presheaf → Presheaf-zipper 0
psh→zipper psh .|F0-<| = tt
psh→zipper psh .|F0-≥| = psh .F0
psh→zipper psh .|Face-≤| = tt
psh→zipper psh .|Face->| = psh .Face
psh→zipper psh .|Coh-≤| = tt
psh→zipper psh .|Coh->| = psh .Face-coh

Presheaf-νSet-< : ∀ m → (F0 : F0-< (2+ m)) (Face : Face-≤ (1+ m) F0) (Coh : Coh-≤ m F0 Face)
             → νSet-< m

Presheaf-νSet-= : ∀ m → (F0 : F0-< (2+ m)) (Face : Face-≤ (1+ m) F0) (Coh : Coh-≤ m F0 Face)
                →  νSet-= m (Presheaf-νSet-< m F0 Face Coh) 

Presheaf-frame : ∀ m → (F0 : F0-< (2+ m)) (Face : Face-≤ (1+ m) F0) (Coh : Coh-≤ m F0 Face)
               → ∀ p {δ} (p≤m :  [ p ≤ m ][ δ ]₂) 
               → F0 .₁ .₂ .Dom
               → frame m p p≤m (Presheaf-νSet-< m F0 Face Coh) .Dom

Presheaf-νSet-< 0 F0 Face Coh = tt
Presheaf-νSet-< (1+ m) F0 Face Coh =
  (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁)) , Presheaf-νSet-= m (F0 .₁) (Face .₁) (Coh .₁)

Presheaf-νSet-= m F0 Face Coh d = 
  HΣ[ d' ∈ F0 .₁ .₂ ]
  H≡ (fullframe (Presheaf-νSet-< m F0 Face Coh))
     d (Presheaf-frame m F0 Face Coh m (◆₂ m) d')

Presheaf-layer : ∀ m → (F0 : F0-< (2+ m)) (Face : Face-≤ (1+ m) F0) (Coh : Coh-≤ m F0 Face)
               → ∀ p {δ} (p≤m :  [ 1+ p ≤ m ][ δ ]₂) 
               → (d : F0 .₁ .₂ .Dom)
               → layer m p p≤m
                   (Presheaf-νSet-< m F0 Face Coh)
                   (Presheaf-frame m F0 Face Coh p (↓₂ p≤m) d) .Dom

Presheaf-painting : ∀ m → (F0 : F0-< (2+ m)) (Face : Face-≤ (1+ m) F0) (Coh : Coh-≤ m F0 Face)
                  → ∀ p {δ} (p≤m :  [ p ≤ m ][ δ ]₂) 
                  → (d : F0 .₁ .₂ .Dom)
                  → painting m p p≤m
                      (Presheaf-νSet-< m F0 Face Coh)
                      (Presheaf-νSet-= m F0 Face Coh)
                      (Presheaf-frame m F0 Face Coh p p≤m d) .Dom

Presheaf-restr-frame : ∀ m → (F0 : F0-< (3+ m)) (Face : Face-≤ (2+ m) F0) (Coh : Coh-≤ (1+ m) F0 Face)
                     → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃) ε
                     → (d : F0 .₁ .₂ .Dom)
                     → Presheaf-frame m (F0 .₁) (Face .₁) (Coh .₁)
                         p (drop₃-2 p≤q≤m) (Face .₁ .₂ q (drop₃-1 p≤q≤m) ε d)
                     ≡ restr-frame m p q p≤q≤m ε
                        (Presheaf-νSet-< (1+ m) F0 Face Coh)
                        (Presheaf-frame (1+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d)

Presheaf-restr-layer : ∀ m → (F0 : F0-< (3+ m)) (Face : Face-≤ (2+ m) F0) (Coh : Coh-≤ (1+ m) F0 Face)
                     → ∀ p q {δ} (p≤q≤m :  [ 1+ p ≤ 1+ q ≤ m ][ δ ]₃) ε
                     → (d : F0 .₁ .₂ .Dom)
                     → subst (λ - → layer m p (drop₃-2 p≤q≤m)
                         (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁))
                         - .Dom)
                       (Presheaf-restr-frame m F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d)
                       (Presheaf-layer m (F0 .₁) (Face .₁) (Coh .₁) p (drop₃-2 p≤q≤m) (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
                     ≡ restr-layer m p q p≤q≤m ε
                         (Presheaf-νSet-< (1+ m) F0 Face Coh)
                         (Presheaf-frame (1+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)
                         (Presheaf-layer (1+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d) 

Presheaf-restr-painting : ∀ m → (F0 : F0-< (3+ m)) (Face : Face-≤ (2+ m) F0) (Coh : Coh-≤ (1+ m) F0 Face)
                        → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃) ε
                        → (d : F0 .₁ .₂ .Dom)
                        → subst (λ - → painting m p (drop₃-2 p≤q≤m)
                            (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁))
                            (Presheaf-νSet-= m (F0 .₁) (Face .₁) (Coh .₁)) 
                            - .Dom)
                          (Presheaf-restr-frame m F0 Face Coh p q p≤q≤m ε d)
                          (Presheaf-painting m (F0 .₁) (Face .₁) (Coh .₁) p (drop₃-2 p≤q≤m)
                            (Face .₁ .₂ q (drop₃-1 p≤q≤m) ε d))
                        ≡ restr-painting m p q p≤q≤m ε
                            (Presheaf-νSet-< (1+ m) F0 Face Coh)
                            (Presheaf-νSet-= (1+ m) F0 Face Coh)
                            (Presheaf-frame (1+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d )
                            (Presheaf-painting (1+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d) 
                            
Presheaf-frame m F0 Face Coh zero   p≤m d = tt
Presheaf-frame m F0 Face Coh (1+ p) p≤m d =
  Presheaf-frame m F0 Face Coh p (↓₂ p≤m) d ,
  Presheaf-layer m F0 Face Coh p p≤m d

Presheaf-layer (1+ m) F0 Face Coh p p≤m d ε =
  subst (λ - → painting m p (⇓₂ p≤m)
                 (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁))
                 (Presheaf-νSet-= m (F0 .₁) (Face .₁) (Coh .₁))
                 - .Dom)
    (Presheaf-restr-frame m F0 Face Coh p p (◆₃ ⇓₂ p≤m) ε d)
    (Presheaf-painting m (F0 .₁) (Face .₁) (Coh .₁) p (⇓₂ p≤m) (Face .₁ .₂ p (⇓₂ p≤m) ε d))

Presheaf-painting m F0 Face Coh p {zero} (ineq₂ Hpn) d with recover-nat-eq p m Hpn
... | refl = d , refl
Presheaf-painting m F0 Face Coh p {1+ δ} (ineq₂ Hpn) d =
  Presheaf-layer m F0 Face Coh p (ineq₂ _) d ,
  Presheaf-painting m F0 Face Coh (1+ p) {δ} (ineq₂ Hpn) d

Presheaf-restr-frame m F0 Face Coh zero q p≤q≤m ε d = refl
Presheaf-restr-frame m F0 Face Coh (1+ p) (1+ q) p≤q≤m ε d =
  Σ-≡→≡ ( Presheaf-restr-frame m F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d
        , Presheaf-restr-layer m F0 Face Coh p q p≤q≤m ε d)
        
Presheaf-restr-layer (1+ m) F0 Face Coh p q p≤q≤m ε d = funExt λ ω →
  subst (λ - → layer (1+ m) p (ineq₂ _)
       (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)) - .Dom)
    (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d)
    (Presheaf-layer (1+ m) (F0 .₁) (Face .₁) (Coh .₁) p (drop₃-2 p≤q≤m) (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) ω
   ≡⟨ subst-application
        (λ - → layer (1+ m) p (ineq₂ _) (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)) - .Dom)
        (λ -₁ -₂ → -₂ ω)
        (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d) ⟩⁻¹
  subst (λ - → painting-m (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)) -))
    (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d) (
  subst painting-m
    (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    (Presheaf-painting m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m)
      (Face .₁ .₁ .₂ p (⇓₂ drop₃-2 p≤q≤m) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))))
   ≡⟨ subst-∘ (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d) _ ⟩
  subst painting-m
    (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
      (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d)) (
  subst painting-m
    (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    (Presheaf-painting m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m)
      (Face .₁ .₁ .₂ p (⇓₂ drop₃-2 p≤q≤m) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))))
   ≡⟨ cong (λ - →
        subst painting-m
          (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
            (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d)) (
        subst painting-m
          (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p p
            (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) -))
      (dcong (Presheaf-painting m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m)) (Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d)) ⟩⁻¹
  subst painting-m
    (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
      (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d)) (
  subst painting-m
    (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) (
  subst (λ - → painting-m (Presheaf-frame m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m) -))
    (Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d)
    (Presheaf-painting m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m)
      (Face .₁ .₁ .₂ q (⇓₂ drop₃-1 p≤q≤m) ε (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))))
   ≡⟨ cong (λ - →
        subst painting-m
          (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
            (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d)) (
        subst painting-m
          (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p p
            (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) -))
        (subst-∘ (Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d) _) ⟩
  subst painting-m
    (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
      (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d)) (
  subst painting-m
    (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p p
      (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) (
  subst painting-m
    (cong (Presheaf-frame m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m))
      (Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d))
    (Presheaf-painting m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m)
      (Face .₁ .₁ .₂ q (⇓₂ drop₃-1 p≤q≤m) ε (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))))  
   ≡⟨ coh₂ {A = frame m p (⇓₂ drop₃-2 p≤q≤m) (Presheaf-νSet-< m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁))}
        (cong (restr-frame m p p (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
          (Presheaf-restr-frame (1+ m) F0 Face Coh p (1+ q) (↓₃ p≤q≤m) ε d))
        (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p p
          (◆₃ (⇓₂ drop₃-2 p≤q≤m)) ω (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
        (cong (Presheaf-frame m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m))
          (Coh .₁ .₂ p q (⇓₃ p≤q≤m) ε ω d))
        (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
          (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d))
        (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
          (Presheaf-restr-frame (1+ m) F0 Face Coh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d))
        (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p q (⇓₃ p≤q≤m) ε
          (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)) ⟩
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
      (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
  subst painting-m
    (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
      (Presheaf-restr-frame (1+ m) F0 Face Coh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)) (
  subst painting-m
    (Presheaf-restr-frame m (F0 .₁) (Face .₁) (Coh .₁) p q (⇓₃ p≤q≤m) ε
      (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))
    (Presheaf-painting m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁) p (⇓₂ drop₃-2 p≤q≤m)
      (Face .₁ .₁ .₂ q (⇓₂ drop₃-1 p≤q≤m) ε (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))))
   ≡⟨ cong (λ - →
        subst painting-m
          (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
            (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
        subst painting-m
          (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
            (Presheaf-restr-frame (1+ m) F0 Face Coh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)) -))
        (Presheaf-restr-painting m (F0 .₁) (Face .₁) (Coh .₁) p q (⇓₃ p≤q≤m) ε
          (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)) ⟩
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
      (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
  subst painting-m
    (cong (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
       (Presheaf-restr-frame (1+ m) F0 Face Coh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d))
    (restr-painting m p q (⇓₃ p≤q≤m) ε
        (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
        (Presheaf-νSet-= (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
        (Presheaf-frame (1+ m) (F0 .₁) (Face .₁) (Coh .₁) p (↑₂ drop₃-2 (⇓₃ p≤q≤m))
           (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))
        (Presheaf-painting (1+ m) (F0 .₁) (Face .₁) (Coh .₁) p (↓₂ drop₃-2 p≤q≤m) (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d)))) 
   ≡⟨ cong (subst painting-m
             (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
               (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)))
           (subst-∘ (Presheaf-restr-frame (1+ m) F0 Face Coh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d) _) ⟩⁻¹
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
      (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)) (
  subst (λ - → painting-m (restr-frame m p q (⇓₃ p≤q≤m) ε (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁)) -))
    (Presheaf-restr-frame (1+ m) F0 Face Coh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)
    (restr-painting m p q (⇓₃ p≤q≤m) ε
        (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
        (Presheaf-νSet-= (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
        (Presheaf-frame (1+ m) (F0 .₁) (Face .₁) (Coh .₁) p (↑₂ drop₃-2 (⇓₃ p≤q≤m))
           (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))
        (Presheaf-painting (1+ m) (F0 .₁) (Face .₁) (Coh .₁) p (↓₂ drop₃-2 p≤q≤m) (Face .₁ .₂ p (↓₂ drop₃-2 p≤q≤m) ω d))))
   ≡⟨ cong (subst painting-m
              (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
                (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)))
            (subst-application (λ - → painting (1+ m) p (↓₂ drop₃-2 p≤q≤m)
                 (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
                 (Presheaf-νSet-= (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
                 - .Dom)
                 (restr-painting m p q (⇓₃ p≤q≤m) ε
                    (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
                    (Presheaf-νSet-= (1+ m) (F0 .₁) (Face .₁) (Coh .₁)))
                 (Presheaf-restr-frame (1+ m) F0 Face Coh p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω d)) ⟩
  subst painting-m
    (coh-frame m p q p (◆₄ ⇓₃ p≤q≤m) ε ω (Presheaf-νSet-< (2+ m) F0 Face Coh)
      (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d))
    (restr-painting m p q (⇓₃ p≤q≤m) ε
      (Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
      (Presheaf-νSet-= (1+ m) (F0 .₁) (Face .₁) (Coh .₁))
      (restr-frame (1+ m) p p (◆₃ ↓₂ drop₃-2 p≤q≤m) ω
        (Presheaf-νSet-< (2+ m) F0 Face Coh)
        (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d))
      (Presheaf-layer (2+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d ω))
   ≡⟨⟩
  restr-layer (1+ m) p q p≤q≤m ε (Presheaf-νSet-< (2+ m) F0 Face Coh)
    (Presheaf-frame (2+ m) F0 Face Coh p (↓₂ ↑₂ drop₃-2 p≤q≤m) d)
    (Presheaf-layer (2+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d) ω ∎
  where
  painting-m : frame m p (⇓₂ drop₃-2 p≤q≤m) (Presheaf-νSet-< m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁)) .Dom → Type
  painting-m d =
    painting m p (⇓₂ drop₃-2 p≤q≤m)
      (Presheaf-νSet-< m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁))
      (Presheaf-νSet-= m (F0 .₁ .₁) (Face .₁ .₁) (Coh .₁ .₁))
      d .Dom

Presheaf-restr-painting m F0 Face Coh p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) ε d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
Presheaf-restr-painting m F0 Face Coh p (1+ q) {1+ δ} p≤q≤m@(ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) ε d =
  subst painting-m
    (Presheaf-restr-frame m F0 Face Coh p (1+ q) p≤q≤m ε d)
    (Presheaf-painting m (F0 .₁) (Face .₁) (Coh .₁) p (drop₃-2 p≤q≤m)
       (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    ≡⟨ subst-Σ (Presheaf-restr-frame m F0 Face Coh p (1+ q) p≤q≤m ε d) ⟩
  subst (λ - → layer m p (drop₃-2 1+p≤q≤m) (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁)) - .Dom)
    (Presheaf-restr-frame m F0 Face Coh p (1+ q) p≤q≤m ε d)
    (Presheaf-layer m (F0 .₁) (Face .₁) (Coh .₁) p (drop₃-2 1+p≤q≤m)
      (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) ,
  subst painting-m'
     (Σ-≡→≡ (Presheaf-restr-frame m F0 Face Coh p (1+ q) p≤q≤m ε d , refl))
     (Presheaf-painting m (F0 .₁) (Face .₁) (Coh .₁) (1+ p) (drop₃-2 1+p≤q≤m)
       (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d))
    ≡⟨ Σ-≡→≡ ( Presheaf-restr-layer m F0 Face Coh p q 1+p≤q≤m ε d
             , subst-Σ' (Presheaf-restr-frame m F0 Face Coh p (1+ q) p≤q≤m ε d)
                         (Presheaf-restr-layer m F0 Face Coh p q 1+p≤q≤m ε d)) ⟩
  restr-layer m p q 1+p≤q≤m ε
    (Presheaf-νSet-< (1+ m) F0 Face Coh)
    (Presheaf-frame (1+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d)
    (Presheaf-layer (1+ m) F0 Face Coh p (⇑₂ drop₃-2 p≤q≤m) d) ,
  subst painting-m'
    (Presheaf-restr-frame m F0 Face Coh (1+ p) (1+ q) 1+p≤q≤m ε d)
    (Presheaf-painting m (F0 .₁) (Face .₁) (Coh .₁) (1+ p) (drop₃-2 1+p≤q≤m)
       (Face .₁ .₂ (1+ q) (drop₃-1 p≤q≤m) ε d)) 
    ≡⟨ Σ-≡→≡ ( refl , Presheaf-restr-painting m F0 Face Coh (1+ p) (1+ q) 1+p≤q≤m ε d) ⟩
  restr-painting m p (1+ q) p≤q≤m ε
    (Presheaf-νSet-< (1+ m) F0 Face Coh)
    (Presheaf-νSet-= (1+ m) F0 Face Coh)
    (Presheaf-frame (1+ m) F0 Face Coh p
      (↑₂ drop₃-2 p≤q≤m) d)
    (Presheaf-painting (1+ m) F0 Face Coh p (↑₂ drop₃-2 p≤q≤m) d) ∎
  where
  1+p≤q≤m : [ 1+ p ≤ 1+ q ≤ m ][ δ ]₃
  1+p≤q≤m = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn
  
  painting-m : frame m p (drop₃-2 p≤q≤m) (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁)) .Dom → Type
  painting-m d =
    painting m p (drop₃-2 p≤q≤m)
      (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁))
      (Presheaf-νSet-= m (F0 .₁) (Face .₁) (Coh .₁))
      d .Dom

  painting-m' : frame m (1+ p) (drop₃-2 1+p≤q≤m) (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁)) .Dom → Type
  painting-m' d =
    painting m (1+ p) (drop₃-2 1+p≤q≤m)
      (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁))
      (Presheaf-νSet-= m (F0 .₁) (Face .₁) (Coh .₁))
      d .Dom

Presheaf-next : ∀ m
              → (zipper : Presheaf-zipper m)
              → νSet-> m (Presheaf-νSet-< m
                            ((zipper .|F0-<| , zipper .|F0-≥| 0) , zipper .|F0-≥| 1)
                            (zipper .|Face-≤| , zipper .|Face->| 0)
                            (zipper .|Coh-≤|))
Presheaf-next m zipper .this =
  Presheaf-νSet-= m
    ((zipper .|F0-<| , zipper .|F0-≥| 0) , zipper .|F0-≥| 1)
    (zipper .|Face-≤| , zipper .|Face->| 0)
    (zipper .|Coh-≤|)
Presheaf-next m zipper .next = Presheaf-next (1+ m) (bump-zipper m zipper)

f : Presheaf → νSet
f psh = Presheaf-next 0 (psh→zipper psh)

Presheaf-getFrame : ∀ m → (F0 : F0-< (2+ m)) (Face : Face-≤ (1+ m) F0) (Coh : Coh-≤ m F0 Face)
                  → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃)
                  → (d : F0 .₁ .₂ .Dom)
                  → getFrame m p q p≤q≤m _ (Presheaf-frame m F0 Face Coh q (drop₃-1 p≤q≤m) d)
                  ≡ Presheaf-frame m F0 Face Coh p (drop₃-2 p≤q≤m) d
Presheaf-getFrame m F0 Face Coh p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
Presheaf-getFrame m F0 Face Coh p (1+ q) {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) d =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in 
  cong ₁ (Presheaf-getFrame m F0 Face Coh (1+ p) (1+ q) {δ} 1+p≤q≤n d)

Presheaf-getPainting : ∀ m → (F0 : F0-< (2+ m)) (Face : Face-≤ (1+ m) F0) (Coh : Coh-≤ m F0 Face)
                     → ∀ p q {δ} (p≤q≤m :  [ p ≤ q ≤ m ][ δ ]₃)
                     → (d : F0 .₁ .₂ .Dom)
                     → getPainting m p q p≤q≤m
                         (Presheaf-νSet-< m F0 Face Coh)
                         (Presheaf-νSet-= m F0 Face Coh)
                         (Presheaf-frame m F0 Face Coh p (drop₃-2 p≤q≤m) d)
                         (Presheaf-painting m F0 Face Coh p (drop₃-2 p≤q≤m) d)
                     ≡ ( Presheaf-frame m F0 Face Coh q (drop₃-1 p≤q≤m) d
                       , Presheaf-painting m F0 Face Coh q (drop₃-1 p≤q≤m) d)
Presheaf-getPainting m F0 Face Coh p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
Presheaf-getPainting m F0 Face Coh p q {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) d =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  Presheaf-getPainting m F0 Face Coh (1+ p) q {δ} 1+p≤q≤n d

Presheaf-νFace : ∀ m → (F0 : F0-< (3+ m)) (Face : Face-≤ (2+ m) F0) (Coh : Coh-≤ (1+ m) F0 Face)
               → ∀ p {δ} (p≤m :  [ p ≤ m ][ δ ]₂) ε
               → (d : F0 .₁ .₂ .Dom)
               → νFace m p p≤m ε _ (Presheaf-frame (1+ m) F0 Face Coh (1+ m) (◆₂ (1+ m)) d)
               ≡ ( Presheaf-frame m (F0 .₁) (Face .₁) (Coh .₁) m (◆₂ m) (Face .₁ .₂ p p≤m ε d)
                 , Face .₁ .₂ p p≤m ε d , refl)
Presheaf-νFace m F0 Face Coh p p≤m ε d =
  νFace m p p≤m ε _ (Presheaf-frame (1+ m) F0 Face Coh (1+ m) (◆₂ (1+ m)) d)
    ≡⟨⟩
  getPainting m p m (◆₃' p≤m) _ _ _
    (getFrame (1+ m) (1+ p) (1+ m) (⇑₃ ◆₃' p≤m) _ (Presheaf-frame (1+ m) F0 Face Coh (1+ m) (◆₂ (1+ m)) d) .₂ ε)
    ≡⟨ cong (λ - → getPainting m p m (◆₃' p≤m) _ _ _ (- .₂ ε))
            (Presheaf-getFrame (1+ m) F0 Face Coh (1+ p) (1+ m) (⇑₃ ◆₃' p≤m) d) ⟩
  getPainting m p m (◆₃' p≤m) _ _ _
    ((Presheaf-frame (1+ m) F0 Face Coh (1+ p) (⇑₂ p≤m) d) .₂ ε)
    ≡⟨  subst-application (λ - → painting m p (⇓₂ (⇑₂ p≤m))
            (Presheaf-νSet-< m (F0 .₁) (Face .₁) (Coh .₁))
            (Presheaf-νSet-= m (F0 .₁) (Face .₁) (Coh .₁)) - .Dom)
            (λ - → getPainting m p m (◆₃' p≤m) _ _ -)
            (Presheaf-restr-frame m F0 Face Coh p p (◆₃ (⇓₂ (⇑₂ p≤m))) ε d) ⟩⁻¹
  subst (λ _ → _)
   (Presheaf-restr-frame m F0 Face Coh p p (◆₃ p≤m) ε d)
   (getPainting m p m (◆₃' p≤m) _ _
    (Presheaf-frame m (F0 .₁) (Face .₁) (Coh .₁) p p≤m (Face .₁ .₂ p (⇓₂ (⇑₂ p≤m)) ε d))
    (Presheaf-painting m (F0 .₁) (Face .₁) (Coh .₁) p p≤m
      (Face .₁ .₂ p p≤m ε d)))
    ≡⟨ subst-const (Presheaf-restr-frame m F0 Face Coh p p (◆₃ p≤m) ε d) _ ⟩ 
  getPainting m p m (◆₃' p≤m) _ _
    (Presheaf-frame m (F0 .₁) (Face .₁) (Coh .₁) p p≤m (Face .₁ .₂ p (⇓₂ (⇑₂ p≤m)) ε d))
    (Presheaf-painting m (F0 .₁) (Face .₁) (Coh .₁) p p≤m
      (Face .₁ .₂ p p≤m ε d))
    ≡⟨ Presheaf-getPainting m (F0 .₁) (Face .₁) (Coh .₁) p m (◆₃' p≤m) (Face .₁ .₂ p p≤m ε d) ⟩
  ( Presheaf-frame m (F0 .₁) (Face .₁) (Coh .₁) m (◆₂ m) (Face .₁ .₂ p p≤m ε d)
  , Face .₁ .₂ p p≤m ε d , refl) ∎

νSet-F0-< : ∀ m → νSet-< m → F0-< m 
νSet-F0-< zero D = tt
νSet-F0-< (1+ m) (D , E) = (νSet-F0-< m D) , (TotalSpace D E)

νSet-Face-≤ : ∀ m → (D : νSet-< (1+ m))
            → Face-≤ m (νSet-F0-< (1+ m) D)
νSet-Face-≤ zero D = tt
νSet-Face-≤ (1+ m) (D , E) = νSet-Face-≤ m D ,  λ p p≤n ε d → νFace m p p≤n ε D (d .₁)

νSet-Coh-≤ : ∀ m → (D : νSet-< (2+ m))
         → Coh-≤ m (νSet-F0-< (2+ m) D) (νSet-Face-≤ (1+ m) D)
νSet-Coh-≤ zero   D = tt
νSet-Coh-≤ (1+ m) ((D , E) , E') = νSet-Coh-≤ m (D , E) , λ p q p≤q≤m ε ω d → νFace-coh m p q p≤q≤m ε ω (D , E) (d .₁)

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
νSet→zipper m D νSet .|Face-≤| = νSet-Face-≤ m (D , νSet .this)
νSet→zipper m D νSet .|Face->| = νSet-Face-> m D νSet
νSet→zipper m D νSet .|Coh-≤| = νSet-Coh-≤ m ((D , νSet .this) , νSet .next .this)
νSet→zipper m D νSet .|Coh->| = νSet-Coh-> m D νSet


f∘g-νSet-< : ∀ m → (D : νSet-< (2+ m))
           → νSet-<-≃ (Presheaf-νSet-< m
                         (νSet-F0-< (2+ m) D)
                         (νSet-Face-≤ (1+ m) D)
                         (νSet-Coh-≤ m D))
                      (D .₁ .₁)

f∘g-νSetₙ : ∀ m
          → (D : νSet-< (2+ m))
          → (d : fullframe (D .₁ .₁) .Dom)
          → (Σ[ d' ∈ TotalSpace (D .₁ .₁) (D .₁ .₂) .Dom ]
          ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
          ≡ Presheaf-frame m _ _ (νSet-Coh-≤ m D) m (◆₂ m) d'))
          ≃ D .₁ .₂ d .Dom

f∘g-frame-≡ : ∀ m
            → (D : νSet-< (2+ m))
            → (d : fullframe (D .₁ .₁) .Dom)
            → (c : D .₁ .₂ d .Dom)
            → subst (λ - → fullframe - .Dom)
                (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
            ≡ Presheaf-frame m
                (νSet-F0-< (2+ m) D)
                (νSet-Face-≤ (1+ m) D)
                (νSet-Coh-≤ m D) m (◆₂ m) (d , c)

f∘g-νSet-< 0 D = ≃[]
f∘g-νSet-< (1+ m) D = f∘g-νSet-< m (D .₁) ≃∷ f∘g-νSetₙ m (D .₁)

f∘g-νSetₙ m D d = f' , (g' , g'∘f'∼id) , (g' , f'∘g'∼id)
 where

 f' : Σ[ d' ∈ TotalSpace (D .₁ .₁) (D .₁ .₂) .Dom ]
    ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
    ≡ Presheaf-frame m _ _ (νSet-Coh-≤ m D) m (◆₂ m) d')
    → D .₁ .₂ d .Dom
 f' ((d' , c) , eq) = subst (λ - → D .₁ .₂ - .Dom) (sym (subst-inj _ (eq ∙ (sym (f∘g-frame-≡ m D d' c))))) c

 g' : D .₁ .₂ d .Dom
    → Σ[ d' ∈ TotalSpace (D .₁ .₁) (D .₁ .₂) .Dom ]
    ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) d
    ≡ Presheaf-frame m _ _ (νSet-Coh-≤ m D) m (◆₂ m) d')
 g' c = (d , c) , f∘g-frame-≡ m D d c
 
 g'∘f'∼id : ∀ c → g' (f' c) ≡ c
 g'∘f'∼id ((d' , c) , coh) = Σ-≡→≡ (Σ-≡→≡ (
    subst-inj _ (coh ∙ (sym (f∘g-frame-≡ m D d' c))) ,
    subst-sym-r (subst-inj (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))) (coh ∙ (sym (f∘g-frame-≡ m D d' c)))) c) ,
    fullframe (Presheaf-νSet-< m (νSet-F0-< (2+ m) D) (νSet-Face-≤ (1+ m) D) (νSet-Coh-≤ m D))
      .has-UIP _ _ _ coh)

 f'∘g'∼id : ∀ c → f' (g' c) ≡ c
 f'∘g'∼id c = cong (λ -₁ → subst (λ - → D .₁ .₂ - .Dom) -₁ c)
              ( cong (sym ∘ (subst-inj (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))))) (trans-sym-r (g' c .₂))
              ∙ J (λ _ eq → sym (subst-inj eq refl) ≡ refl) refl (sym (νSet-<-≃→≡ (f∘g-νSet-< m D))))

f∘g-frame-≡ zero D d c = refl
f∘g-frame-≡ (1+ m) D d c = νFace-≡ m _ _ _ λ p p≤n ε →
   νFace m p p≤n ε
    (Presheaf-νSet-< (1+ m) (νSet-F0-< (3+ m) D) (νSet-Face-≤ (2+ m) D)
     (νSet-Coh-≤ (1+ m) D))
    (subst (λ - → fullframe - .Dom)
     (sym (νSet-<-≃→≡ (f∘g-νSet-< (1+ m) D))) d)
    ≡⟨ νFace-νSet-<-≃ m _ _ _ _ (f∘g-νSet-< m (D .₁)) (f∘g-νSetₙ m (D .₁)) d p p≤n ε  ⟩
  subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< m (D .₁)))) (νFace m p p≤n ε _ d .₁) ,
  νFace m p p≤n ε (D .₁ .₁) d ,
  f∘g-frame-≡ m (D .₁) (νFace m p p≤n ε (D .₁ .₁) d .₁) (νFace m p p≤n ε (D .₁ .₁) d .₂)
    ≡⟨  J' (λ a eq → (a , νFace m p p≤n ε (D .₁ .₁) d , eq)
                  ≡ (Presheaf-frame m
                      (νSet-F0-< (3+ m) D .₁) (νSet-Face-≤ (2+ m) D .₁)
                      (νSet-Coh-≤ (1+ m) D .₁) m (◆₂ m)
                      (νFace m p p≤n ε (D .₁ .₁) d) ,
                    νFace m p p≤n ε (D .₁ .₁) d ,
                    refl))
           refl
           (f∘g-frame-≡ m (D .₁) (νFace m p p≤n ε (D .₁ .₁) d .₁) (νFace m p p≤n ε (D .₁ .₁) d .₂))  ⟩
  Presheaf-frame m
    (νSet-F0-< (3+ m) D .₁) (νSet-Face-≤ (2+ m) D .₁)
    (νSet-Coh-≤ (1+ m) D .₁) m (◆₂ m)
    (νFace m p p≤n ε (D .₁ .₁) d) ,
  νFace m p p≤n ε (D .₁ .₁) d ,
  refl
    ≡⟨ Presheaf-νFace m _ _ _ p p≤n ε (d , c) ⟩⁻¹
  νFace m p p≤n ε
    (Presheaf-νSet-< (1+ m) (νSet-F0-< (3+ m) D) (νSet-Face-≤ (2+ m) D)
      (νSet-Coh-≤ (1+ m) D))
    (Presheaf-frame (1+ m)
       (νSet-F0-< (3+ m) D)
       (νSet-Face-≤ (2+ m) D)
       (νSet-Coh-≤ (1+ m) D) (1+ m) (◆₂ (1+ m)) (d , c)) ∎

f∘g-νSet-> : ∀ m → (D : νSet-< m) (νSet : νSet-> m D)
           → νSet->-≃ (f∘g-νSet-< m ((D , νSet .this) , νSet .next .this))
              (Presheaf-next m (νSet→zipper m D νSet))
              νSet
f∘g-νSet-> m D νSet .this-≃ = f∘g-νSetₙ m ((D , νSet .this) , νSet .next .this)
f∘g-νSet-> m D νSet .next-≃ = f∘g-νSet-> (1+ m) (D , νSet .this) (νSet .next)

g∘f-F0 : ∀ m → (zipper : Presheaf-zipper m)
       → ∀ n
       → νSet-F0-≥ m
           (Presheaf-νSet-< m _ _ (zipper .|Coh-≤|))
           (Presheaf-next m zipper)
           n .Dom
       ≃ zipper .|F0-≥| n .Dom
g∘f-F0 m zipper (1+ n) = g∘f-F0 (1+ m) (bump-zipper m zipper) n
g∘f-F0 m zipper 0 = f' , (g' , g'∘f'∼id ) , (g' , f'∘g'∼id)
  where
  f' : TotalSpace
        (Presheaf-νSet-< m _ _ (zipper .|Coh-≤|))
        (Presheaf-νSet-= m _ _ (zipper .|Coh-≤|))
        .Dom
     → zipper .|F0-≥| 0 .Dom
  f' (d , (c , eq)) = c

  g' : zipper .|F0-≥| 0 .Dom
     → TotalSpace
        (Presheaf-νSet-< m _ _ (zipper .|Coh-≤|))
        (Presheaf-νSet-= m _ _ (zipper .|Coh-≤|))
        .Dom
  g' d = _ , (d , refl)

  g'∘f'∼id : ∀ c → g' (f' c) ≡ c
  g'∘f'∼id (d , c , refl) = refl

  f'∘g'∼id : ∀ c → f' (g' c) ≡ c
  f'∘g'∼id c = refl

g∘f-Face : ∀ m → (zipper : Presheaf-zipper m)
         → ∀ n p {δ} (p≤n : [ p ≤ n + m ][ δ ]₂) ε
         → (d : νSet-F0-≥ (1+ m)
                  (Presheaf-νSet-< (1+ m)
                     (_ , zipper .|F0-≥| 2)
                     (_ , (zipper .|Face->| 1))
                     (_ , zipper .|Coh->| 0))
                  (Presheaf-next (1+ m) (bump-zipper m zipper))
                  n .Dom)
         → g∘f-F0 m zipper n .₁
           (νSet-Face-> m
              (Presheaf-νSet-< m _ _ (zipper .|Coh-≤|))
              (Presheaf-next m zipper)
              n p p≤n ε d)
         ≡ zipper .|Face->| n p p≤n ε
            (g∘f-F0 m zipper (1+ n) .₁ d) 
g∘f-Face m zipper (1+ n) = g∘f-Face (1+ m) (bump-zipper m zipper) n
g∘f-Face m zipper zero p p≤n ε (d , (c , eq)) =
  (νFace m p p≤n ε (Presheaf-νSet-< (1+ m) (_ , zipper .|F0-≥| 2) (_ , (zipper .|Face->| 1)) (_ , zipper .|Coh->| 0))
    d) .₂ .₁
    ≡⟨ cong (λ - → (νFace m p p≤n ε _ -) .₂ .₁) eq ⟩
  (νFace m p p≤n ε (Presheaf-νSet-< (1+ m) (_ , zipper .|F0-≥| 2) (_ , (zipper .|Face->| 1)) (_ , zipper .|Coh->| 0))
    (Presheaf-frame (1+ m)
      (_ , zipper .|F0-≥| 2)
      (_ , (zipper .|Face->| 1))
      (_ , zipper .|Coh->| 0)
      (1+ m) (◆₂ (1+ m)) c)) .₂ .₁
    ≡⟨ cong (λ - → - .₂ .₁)
         (Presheaf-νFace m (_ , zipper .|F0-≥| 2) (_ , (zipper .|Face->| 1)) (_ , zipper .|Coh->| 0)
         p p≤n ε c) ⟩
  zipper .|Face->| zero p p≤n ε c ∎

f∘g : ∀ νSet → νSet-≃ (f (g νSet)) νSet 
f∘g νSet = f∘g-νSet-> 0 tt νSet

g∘f : ∀ psh → g (f psh) ≡ psh
g∘f psh = Presheaf-≃ (g (f psh)) psh
           (g∘f-F0 0 (psh→zipper psh))
           (g∘f-Face 0 (psh→zipper psh))
