{-# OPTIONS --termination-depth=3 #-}

open import Prelude

module Bonak
  (fe : {A : Set} {B : A → Set}
      → (f g : (a : A) → B a)
      → (∀ a → f a ≡ g a)
      → f ≡ g)
  (fe-≡ : {A : Set} {B : A → Set}
        → (f g : (a : A) → B a)
        → (p : f ≡ g)
        → fe f g (λ a → cong-app p a) ≡ p)
  (arity : Type)
 where

open import HSet
open import Inequalities

open HΠ fe fe-≡

postulate
 admit : ∀ {ℓ} {A : Set ℓ} → A

coh₂ : ∀ {A : HSet} {B : A .Dom → Type}
     → {a a₁ a₁' a₂ a₂' a' : A .Dom} {b : B a}
     → (H₁ : a₁' ≡ a') (H₁' : a₁ ≡ a₁') (H₁'' : a ≡ a₁)
       (H₂ : a₂' ≡ a') (H₂' : a₂ ≡ a₂') (H₂'' : a ≡ a₂)
     → subst B H₁ (
       subst B H₁' (
       subst B H₁'' b))
     ≡ subst B H₂ (
       subst B H₂' (
       subst B H₂'' b))
coh₂ {A} {B} {b = b} refl refl refl refl refl H₂'' =
 cong (λ - → subst B - b) (A .has-UIP refl H₂'')

νSet-< : ℕ → Type₁
νSet-= : (n : ℕ) → νSet-< n → Type₁

νSet-< zero   = ⊤
νSet-< (1+ n) = Σ[ R ∈ νSet-< n ] νSet-= n R

frame : ∀ n p → (p≤n : [ p ≤ n ]₂)
      → (D : νSet-< n)
      → HSet
        
layer : ∀ n p → (p≤n : [ 1+ p ≤ n ]₂)
      → (D : νSet-< n)
      → (d : frame n p (↓₂ p≤n) D .Dom)
      → HSet

painting : ∀ n p → (p≤n : [ p ≤ n ]₂)
         → (D : νSet-< n) (E : νSet-= n D)
         → (d : frame n p p≤n D .Dom)
         → HSet

restr-frame : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃)
            → (ε : arity)
            → (D : νSet-< (1+ n))
            → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
            → frame n p (drop₃-2 p≤q≤n) (D .₁) .Dom

restr-layer : ∀ n p q → (p≤q<n : [ 1+ p ≤ 1+ q ≤ n ]₃)
            → (ε : arity)
            → (D : νSet-< (1+ n))
            → (d : frame (1+ n) p (↑₂ ↓₂ drop₃-2 p≤q<n) D .Dom)
            → (l : layer (1+ n) p (↑₂ drop₃-2 p≤q<n) D d .Dom)
            → layer n p (drop₃-2 p≤q<n) (D .₁) (restr-frame n p (1+ q) (↓₃ p≤q<n) ε D d) .Dom

restr-painting : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃)
               → (ε : arity)
               → (D : νSet-< (1+ n)) (E : νSet-= (1+ n) D)
               → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
               → (c : painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D E d .Dom)
               → painting n p (drop₃-2 p≤q≤n) (D .₁) (D .₂)
                  (restr-frame n p q p≤q≤n ε D d) .Dom

coh-frame : ∀ n p q r → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄)
          → (ε ω : arity)
          → (D : νSet-< (2+ n))
          → (d : frame (2+ n) p (↑₂ ↑₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
          → restr-frame n p q (drop₄-2 p≤r≤q≤n) ε (D .₁)
              (restr-frame (1+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d)
          ≡ restr-frame n p r (drop₄-3 p≤r≤q≤n) ω (D .₁)
              (restr-frame (1+ n) p (1+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D d)

coh-layer : ∀ n p q r → (p≤r≤q≤n : [ 1+ p ≤ 1+ r ≤ 1+ q ≤ n ]₄)
          → (ε ω : arity)
          → (D : νSet-< (2+ n))
          → (d : frame (2+ n) p (↑₂ ↑₂ ↓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
          → (l : layer (2+ n) p (↑₂ ↑₂ drop₃-2 (drop₄-2 p≤r≤q≤n) ) D d .Dom)
          → subst (λ - → layer n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁) - .Dom)
              (coh-frame n p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d)
              (restr-layer n p q (drop₄-2 p≤r≤q≤n) ε (D .₁) _
                (restr-layer (1+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d l))
          ≡ restr-layer n p r (drop₄-3 p≤r≤q≤n) ω (D .₁) _
              (restr-layer (1+ n) p (1+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D d l)

coh-painting : ∀ n p q r → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄)
             → (ε ω : arity)
             → (D : νSet-< (2+ n)) (E : νSet-= (2+ n) D)  
             → (d : frame (2+ n) p (↑₂ ↑₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
             → (c : painting (2+ n) p (↑₂ ↑₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) D E d .Dom)
             → subst (λ - → painting n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁) (D .₁ .₂) - .Dom)
                 (coh-frame n p q r p≤r≤q≤n ε ω D d)
                   (restr-painting n p q (drop₄-2 p≤r≤q≤n) ε (D .₁) (D .₂) _
                     (restr-painting (1+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D E d c))
             ≡ restr-painting n p r (drop₄-3 p≤r≤q≤n) ω (D .₁) (D .₂) _
                 (restr-painting (1+ n) p (1+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D E d c)

νSet-= n D = frame n n (◆₂ n) D .Dom → HSet 

frame n zero   p≤n D = HUnit
frame n (1+ p) p≤n D = HΣ[ d ∈ frame n p (↓₂ p≤n) D ] layer n p p≤n D d

layer (1+ n) p p≤n D d =
 HΠ[ ε ∈ arity ] painting n p (⇓₂ p≤n) (D .₁) (D .₂) ( restr-frame n p p (◆₃ ⇓₂ p≤n) ε D d)

I : ∀ n p δ (p≤n : [ p ≤ n ]₂)
  → δ ≡ p≤n .δpn
  → (D : νSet-< n) (E : νSet-= n D)
  → frame n p p≤n D .Dom → HSet
I n p zero (ineq₂ δpn Hpn) refl D E d with recover-nat-eq' p n Hpn
... | refl = E d
I n p (1+ δ) (ineq₂ _ Hpn) refl D E d =
  let 1+p≤n = ineq₂ δ Hpn in 
  HΣ[ l ∈ layer n p 1+p≤n D d ] I n (1+ p) δ 1+p≤n refl D E (d , l)
painting n p p≤n D E = I n p (p≤n .δpn) p≤n refl D E

restr-frame n zero q p≤q≤n ε D d   = tt
restr-frame n (1+ p) (1+ q) p≤q≤n ε D (d , l) =
 restr-frame n p (1+ q) (↓₃ p≤q≤n) ε D d ,
 restr-layer n p q p≤q≤n ε D d l

restr-layer (1+ n) p q p≤q≤n ε (D , E) d l ω =
  subst (λ - → painting n p (⇓₂ drop₃-2 p≤q≤n) (D .₁) (D .₂) - .Dom)
    (coh-frame n p q p (◆₄ ⇓₃ p≤q≤n) ε ω (D , E) d)
    (restr-painting n p q (⇓₃ p≤q≤n) ε D E _ (l ω))

II : ∀ n p q δ → (p≤q≤n : [ p ≤ q ≤ n ]₃)
   → δ ≡ p≤q≤n .δpq
   → (ε : arity)
   → (D : νSet-< (1+ n)) (E : νSet-= (1+ n) D)
   → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
   → (c : painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D E d .Dom)
   → painting n p (drop₃-2 p≤q≤n) (D .₁) (D .₂)
       (restr-frame n p q p≤q≤n ε D d) .Dom
II n p q zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl ε D E d (l , c)
 with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
... | refl | refl = l ε
II n p (1+ q) (1+ δ) p≤q≤n@(ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl ε D E d (l , c) =
    let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
    (restr-layer n p q 1+p≤q≤n ε D _ l) , II n (1+ p) (1+ q) δ 1+p≤q≤n refl ε D E (d , l) c

restr-painting n p q p≤q≤n = II n p q _ p≤q≤n refl

coh-frame n zero q r p≤r≤q≤n ε ω D d = refl
coh-frame n (1+ p) (1+ q) (1+ r) p≤r≤q≤n ε ω D (d , l) =
  Σ-≡→≡ (coh-frame n p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d ,
         coh-layer n p q r p≤r≤q≤n ε ω D d l)

coh-layer (1+ n) p q r p≤r≤q≤n ε ω D d l = fe _ _ (λ θ → helper θ)
 where
  helper : (θ : arity)
         → subst (λ - → layer (1+ n) p (drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁) - .Dom)
              (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d)
              (restr-layer (1+ n) p q (drop₄-2 p≤r≤q≤n) ε (D .₁) _
                (restr-layer (2+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d l)) θ
          ≡ restr-layer (1+ n) p r (drop₄-3 p≤r≤q≤n) ω (D .₁) _
              (restr-layer (2+ n) p (1+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D d l) θ
  helper θ =
   subst (λ - → layer (1+ n) p (drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁) - .Dom)
     (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d) (
   restr-layer (1+ n) p q (drop₄-2 p≤r≤q≤n) ε (D .₁) _
     (restr-layer (2+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d l)) θ
     ≡⟨ subst-application (λ - → layer (1+ n) p _ _ - .Dom) (λ -₁ -₂ → -₂ θ)
           (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d) ⟩⁻¹
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂)
                   (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁) -) .Dom)
         (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d) (
   restr-layer (1+ n) p q (drop₄-2 p≤r≤q≤n) ε (D .₁) _
     (restr-layer (2+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d l) θ)
     ≡⟨ subst-∘ (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d) ⟩
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (cong (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁))
         (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d)) (
   restr-layer (1+ n) p q (drop₄-2 p≤r≤q≤n) ε (D .₁) _
     (restr-layer (2+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d l) θ)
     ≡⟨ cong (λ - → subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                      (cong (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁))
                        (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d)) (
                    subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                      (coh-frame n p q p (◆₄ (⇓₃ drop₄-2 p≤r≤q≤n)) ε θ (D .₁)
                        (restr-frame (2+ n) p (1+ r) (↓₃ ↑₃ drop₄-3 p≤r≤q≤n) ω D d)) -))
         (subst-application _
           (restr-painting n p q (⇓₃ drop₄-2 p≤r≤q≤n) ε (D .₁ .₁) (D .₁ .₂))
           (coh-frame (1+ n) p r p ((◆₄ (↓₃' drop₄-3 p≤r≤q≤n))) ω θ D d)) ⟩⁻¹
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (cong (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁))
        (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (coh-frame n p q p (◆₄ (⇓₃ drop₄-2 p≤r≤q≤n)) ε θ (D .₁)
        (restr-frame (2+ n) p (1+ r) (↓₃ ↑₃ drop₄-3 p≤r≤q≤n) ω D d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂)
                  (restr-frame n p q (⇓₃ (drop₄-2 p≤r≤q≤n)) ε (D .₁ .₁) -) .Dom)
     (coh-frame (1+ n) p r p ((◆₄ (↓₃' drop₄-3 p≤r≤q≤n))) ω θ D d) (
   restr-painting n p q (⇓₃ drop₄-2 p≤r≤q≤n) ε (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p r (↓₃' drop₄-3 p≤r≤q≤n) ω (D .₁) (D .₂) _ (l θ)))))
     ≡⟨ cong (λ - → subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                      (cong (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁))
                        (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d)) (
                    subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                      (coh-frame n p q p (◆₄ (⇓₃ drop₄-2 p≤r≤q≤n)) ε θ (D .₁)
                        (restr-frame (2+ n) p (1+ r) (↓₃ ↑₃ drop₄-3 p≤r≤q≤n) ω D d)) -))
        (subst-∘ (coh-frame (1+ n) p r p ((◆₄ (↓₃' drop₄-3 p≤r≤q≤n))) ω θ D d)) ⟩
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (cong (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁))
        (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (coh-frame n p q p (◆₄ (⇓₃ drop₄-2 p≤r≤q≤n)) ε θ (D .₁)
        (restr-frame (2+ n) p (1+ r) (↓₃ ↑₃ drop₄-3 p≤r≤q≤n) ω D d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (cong (restr-frame n p q (⇓₃ (drop₄-2 p≤r≤q≤n)) ε (D .₁ .₁))
        (coh-frame (1+ n) p r p ((◆₄ (↓₃' drop₄-3 p≤r≤q≤n))) ω θ D d)) (
   restr-painting n p q (⇓₃ drop₄-2 p≤r≤q≤n) ε (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p r (↓₃' drop₄-3 p≤r≤q≤n) ω (D .₁) (D .₂) _ (l θ)))))
     ≡⟨ coh₂ {A = frame n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁)}
             (cong (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁))
               (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d))
             (coh-frame n p q p (◆₄ (⇓₃ drop₄-2 p≤r≤q≤n)) ε θ (D .₁)
               (restr-frame (2+ n) p (1+ r) (↓₃ ↑₃ drop₄-3 p≤r≤q≤n) ω D d))
             (cong (restr-frame n p q (⇓₃ (drop₄-2 p≤r≤q≤n)) ε (D .₁ .₁))
               (coh-frame (1+ n) p r p ((◆₄ (↓₃' drop₄-3 p≤r≤q≤n))) ω θ D d))
             (coh-frame n p r p (◆₄ (⇓₃ (drop₄-3 p≤r≤q≤n))) ω θ (D .₁)
               (restr-frame (2+ n) p (2+ q) (↓₃ ↑₃' (drop₄-2 p≤r≤q≤n)) ε D d))
             (cong (restr-frame n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁)) 
               (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d))
             (coh-frame n p q r (⇓₄ p≤r≤q≤n) ε ω (D .₁)
               (restr-frame (2+ n) p p (◆₃ (↑₂ ↓₂ drop₃-2 (drop₄-2 p≤r≤q≤n))) θ D d)) ⟩
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (coh-frame n p r p (◆₄ (⇓₃ (drop₄-3 p≤r≤q≤n))) ω θ (D .₁)
         (restr-frame (2+ n) p (2+ q) (↓₃ ↑₃' (drop₄-2 p≤r≤q≤n)) ε D d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (cong (restr-frame n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁)) 
       (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (coh-frame n p q r (⇓₄ p≤r≤q≤n) ε ω (D .₁)
         (restr-frame (2+ n) p p (◆₃ (↑₂ ↓₂ drop₃-2 (drop₄-2 p≤r≤q≤n))) θ D d)) (
   restr-painting n p q (⇓₃ drop₄-2 p≤r≤q≤n) ε (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p r (↓₃' drop₄-3 p≤r≤q≤n) ω (D .₁) (D .₂) _ (l θ)))))
     ≡⟨ cong (λ - → subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                      (coh-frame n p r p (◆₄ (⇓₃ (drop₄-3 p≤r≤q≤n))) ω θ (D .₁)
                        (restr-frame (2+ n) p (2+ q) (↓₃ ↑₃' (drop₄-2 p≤r≤q≤n)) ε D d)) (
                    subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                      (cong (restr-frame n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁)) 
                        (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d)) -))
          (coh-painting n p q r (⇓₄ p≤r≤q≤n) ε ω (D .₁) (D .₂) _ (l θ)) ⟩
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (coh-frame n p r p (◆₄ (⇓₃ (drop₄-3 p≤r≤q≤n))) ω θ (D .₁)
         (restr-frame (2+ n) p (2+ q) (↓₃ ↑₃' (drop₄-2 p≤r≤q≤n)) ε D d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (cong (restr-frame n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁)) 
       (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d)) (
     restr-painting n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁) (D .₁ .₂) _
       (restr-painting (1+ n) p (1+ q) (↓₃ (drop₄-2 p≤r≤q≤n)) ε (D .₁) (D .₂) _ (l θ))))
     ≡⟨ cong (subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
               (coh-frame n p r p (◆₄ (⇓₃ (drop₄-3 p≤r≤q≤n))) ω θ (D .₁ .₁ , D .₁ .₂)
                 (restr-frame (2+ n) p (2+ q) (↓₃ ↑₃' (drop₄-2 p≤r≤q≤n)) ε D d)))
        (subst-∘ (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d)) ⟩⁻¹
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
     (coh-frame n p r p (◆₄ (⇓₃ (drop₄-3 p≤r≤q≤n))) ω θ (D .₁)
         (restr-frame (2+ n) p (2+ q) (↓₃ ↑₃' (drop₄-2 p≤r≤q≤n)) ε D d)) (
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂)
                  (restr-frame n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁) -) .Dom)
     (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d) (
     restr-painting n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁) (D .₁ .₂) _
       (restr-painting (1+ n) p (1+ q) (↓₃ (drop₄-2 p≤r≤q≤n)) ε (D .₁) (D .₂) _ (l θ))))
     ≡⟨ cong (subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
               (coh-frame n p r p (◆₄ (⇓₃ (drop₄-3 p≤r≤q≤n))) ω θ (D .₁ .₁ , D .₁ .₂)
                 (restr-frame (2+ n) p (2+ q) (↓₃ ↑₃' (drop₄-2 p≤r≤q≤n)) ε D d)))
         (subst-application _ (restr-painting n p r (⇓₃ (drop₄-3 p≤r≤q≤n)) ω (D .₁ .₁) (D .₁ .₂))
             (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d)) ⟩
   restr-layer (1+ n) p r (drop₄-3 p≤r≤q≤n) ω (D .₁) _
      (restr-layer (2+ n) p (1+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D d l) θ ∎

III : ∀ n p q r δ → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄)
    → δ ≡ p≤r≤q≤n .δpr
    → (ε ω : arity)
    → (D : νSet-< (2+ n)) (E : νSet-= (2+ n) D)  
    → (d : frame (2+ n) p (↑₂ ↑₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
    → (c : painting (2+ n) p (↑₂ ↑₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) D E d .Dom)
    → subst (λ - → painting n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁) (D .₁ .₂) - .Dom)
        (coh-frame n p q r p≤r≤q≤n ε ω D d)
        (restr-painting n p q (drop₄-2 p≤r≤q≤n) ε (D .₁) (D .₂) _
            (restr-painting (1+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D E d c))
    ≡ restr-painting n p r (drop₄-3 p≤r≤q≤n) ω (D .₁) (D .₂) _
        (restr-painting (1+ n) p (1+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D E d c)
III n p q r zero (ineq₄ δpr δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) refl ε ω D E d c
  with recover-nat-eq' p r Hpr | recover-nat-eq' δrq δpq Hprq | recover-nat-eq' δrn δpn Hprn
... | refl | refl | refl = refl
III n p (1+ q) (1+ r) (1+ δ) p≤r≤q≤n@(ineq₄ _ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn)
 refl ε ω D E d (l , c) =
   let 1+p≤r≤q≤n = ineq₄ δ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn in
   let rec = III n (1+ p) (1+ q) (1+ r) δ 1+p≤r≤q≤n refl ε ω D E (d , l) c in
   subst (λ - → painting n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁) (D .₁ .₂) - .Dom)
     (coh-frame n p (1+ q) (1+ r) p≤r≤q≤n ε ω D d)
     (restr-painting n p (1+ q) (drop₄-2 p≤r≤q≤n) ε (D .₁) (D .₂) _
       (restr-painting (1+ n) p (1+ r) (↑₃ drop₄-3 p≤r≤q≤n) ω D E d (l , c)))
     ≡⟨ subst-Σ (coh-frame n p (1+ q) (1+ r) p≤r≤q≤n ε ω D d) ⟩
   subst (λ - → layer n p (drop₃-2 (drop₄-2 1+p≤r≤q≤n)) (D .₁ .₁) - .Dom)
     (coh-frame n p (1+ q) (1+ r) p≤r≤q≤n ε ω D d)
     (restr-layer n p q (drop₄-2 1+p≤r≤q≤n) ε (D .₁) _
        (restr-layer (1+ n) p r (↑₃ drop₄-3 1+p≤r≤q≤n) ω D d l)) ,
     subst (λ v → painting n (1+ p) (drop₃-2 (drop₄-2 1+p≤r≤q≤n)) (D .₁ .₁) (D .₁ .₂) v .Dom)
     (Σ-≡→≡ (coh-frame n p (1+ q) (1+ r) p≤r≤q≤n ε ω D d , refl))
       (restr-painting n (1+ p) (1+ q) (drop₄-2 1+p≤r≤q≤n) ε (D .₁) (D .₂) _
         (restr-painting (1+ n) (1+ p) (1+ r) (↑₃ drop₄-3 1+p≤r≤q≤n) ω D E (d , l) c))
     ≡⟨ Σ-≡→≡ (coh-layer n p q r 1+p≤r≤q≤n ε ω _ d l ,
               subst-Σ' (coh-frame n p (1+ q) (1+ r) _ ε ω D d)
                        (coh-layer n p q r 1+p≤r≤q≤n ε ω _ d l))⟩
    (restr-layer n p r (drop₄-3 1+p≤r≤q≤n) ω (D .₁) _
      (restr-painting (1+ n) p (2+ q) _ ε D E d (l , c) .₁)) ,
    subst (λ - → painting n (1+ p) _ (D .₁ .₁) (D .₁ .₂) - .Dom)
     (Σ-≡→≡ (coh-frame n p (1+ q) (1+ r) _ ε ω D d ,
             coh-layer n p q r 1+p≤r≤q≤n ε ω D d l))
     (restr-painting n (1+ p) (1+ q) (drop₄-2 1+p≤r≤q≤n) ε (D .₁) (D .₂) _
      (restr-painting (1+ n) (1+ p) (1+ r) (↑₃ drop₄-3 1+p≤r≤q≤n) ω D E (d , l) c))
     ≡⟨ Σ-≡→≡ (refl , rec) ⟩
   restr-painting n p (1+ r) (drop₄-3 p≤r≤q≤n) ω (D .₁) (D .₂) _
      (restr-painting (1+ n) p (2+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D E d (l , c)) ∎
coh-painting n p q r p≤r≤q≤n = III n p q r _ p≤r≤q≤n refl

record νSet-> (n : ℕ) (D : νSet-< n) : Type₁ where
 coinductive
 field
   this : νSet-= n D
   next : νSet-> (1+ n) (D , this)
open νSet-> public


νSet : Type₁
νSet = νSet-> 0 tt 
