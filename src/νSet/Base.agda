{-# OPTIONS --termination-depth=3 #-}

open import Prelude
open import Axioms.FunExt

module νSet.Base
  (fe : FunExt-Axiom)
  (arity : Type)
 where

open import HSet
open import Inequalities

open HSet-FE fe
open FE fe

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
 cong (λ - → subst B - b) (A .has-UIP _ _ refl H₂'')

νSet-< : ℕ → Type₁
νSet-= : (n : ℕ) → νSet-< n → Type₁

νSet-< zero   = ⊤
νSet-< (1+ n) = Σ[ R ∈ νSet-< n ] νSet-= n R

frame : ∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
      → (D : νSet-< n)
      → HSet
         
layer : ∀ n p {δ} → (p≤n : [ 1+ p ≤ n ][ δ ]₂)
      → (D : νSet-< n)
      → (d : frame n p (↓₂ p≤n) D .Dom)
      → HSet

painting : ∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
         → (D : νSet-< n) (E : νSet-= n D)
         → (d : frame n p p≤n D .Dom)
         → HSet

restr-frame : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
            → (ε : arity)
            → (D : νSet-< (1+ n))
            → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
            → frame n p (drop₃-2 p≤q≤n) (D .₁) .Dom

restr-layer : ∀ n p q {δ} → (p≤q<n : [ 1+ p ≤ 1+ q ≤ n ][ δ ]₃)
            → (ε : arity)
            → (D : νSet-< (1+ n))
            → (d : frame (1+ n) p (↑₂ ↓₂ drop₃-2 p≤q<n) D .Dom)
            → (l : layer (1+ n) p (↑₂ drop₃-2 p≤q<n) D d .Dom)
            → layer n p (drop₃-2 p≤q<n) (D .₁) (restr-frame n p (1+ q) (↓₃ p≤q<n) ε D d) .Dom

restr-painting : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
               → (ε : arity)
               → (D : νSet-< (1+ n)) (E : νSet-= (1+ n) D)
               → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
               → (c : painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D E d .Dom)
               → painting n p (drop₃-2 p≤q≤n) (D .₁) (D .₂)
                  (restr-frame n p q p≤q≤n ε D d) .Dom

coh-frame : ∀ n p q r {δ} → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ][ δ ]₄)
          → (ε ω : arity)
          → (D : νSet-< (2+ n))
          → (d : frame (2+ n) p (↑₂ ↑₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
          → restr-frame n p q (drop₄-2 p≤r≤q≤n) ε (D .₁)
              (restr-frame (1+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d)
          ≡ restr-frame n p r (drop₄-3 p≤r≤q≤n) ω (D .₁)
              (restr-frame (1+ n) p (1+ q) (↑₃' drop₄-2 p≤r≤q≤n) ε D d)

coh-layer : ∀ n p q r {δ} → (p≤r≤q≤n : [ 1+ p ≤ 1+ r ≤ 1+ q ≤ n ][ δ ]₄)
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

coh-painting : ∀ n p q r {δ} → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ][ δ ]₄)
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

painting n p {zero} (ineq₂ Hpn) D E d with recover-nat-eq p n Hpn
... | refl = E d
painting n p {1+ δ} (ineq₂ Hpn) D E d =
  let 1+p≤n = ineq₂ Hpn in 
  HΣ[ l ∈ layer n p 1+p≤n D d ] painting n (1+ p) {δ} 1+p≤n D E (d , l)

restr-frame n zero q p≤q≤n ε D d   = tt
restr-frame n (1+ p) (1+ q) p≤q≤n ε D (d , l) =
 restr-frame n p (1+ q) (↓₃ p≤q≤n) ε D d ,
 restr-layer n p q p≤q≤n ε D d l

restr-layer (1+ n) p q p≤q≤n ε (D , E) d l ω =
  subst (λ - → painting n p (⇓₂ drop₃-2 p≤q≤n) (D .₁) (D .₂) - .Dom)
    (coh-frame n p q p (◆₄ ⇓₃ p≤q≤n) ε ω (D , E) d)
    (restr-painting n p q (⇓₃ p≤q≤n) ε D E _ (l ω))

restr-painting n p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) ε D E d (l , c)
 with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = l ε
restr-painting n p (1+ q) {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) ε D E d (l , c) =
    let 1+p≤q≤n = (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) in
    (restr-layer n p q 1+p≤q≤n ε D _ l) ,
    (restr-painting n (1+ p) (1+ q) {δ} 1+p≤q≤n ε D E (d , l) c)

coh-frame n zero q r p≤r≤q≤n ε ω D d = refl
coh-frame n (1+ p) (1+ q) (1+ r) p≤r≤q≤n ε ω D (d , l) =
  Σ-≡→≡ (coh-frame n p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d ,
         coh-layer n p q r p≤r≤q≤n ε ω D d l)

coh-layer (1+ n) p q r p≤r≤q≤n ε ω D d l = funExt (λ θ → helper θ)
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
     ≡⟨ subst-application (λ - → layer (1+ n) p (drop₃-2 (drop₄-2 p≤r≤q≤n)) _ - .Dom) (λ -₁ -₂ → -₂ θ)
           (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d) ⟩⁻¹
   subst (λ - → painting n p (⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) (D .₁ .₁ .₁) (D .₁ .₁ .₂)
                   (restr-frame n p p (◆₃ ⇓₂ drop₃-2 (drop₄-2 p≤r≤q≤n)) θ (D .₁ .₁) -) .Dom)
         (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d) (
   restr-layer (1+ n) p q (drop₄-2 p≤r≤q≤n) ε (D .₁) _
     (restr-layer (2+ n) p r (↑₃ drop₄-3 p≤r≤q≤n) ω D d l) θ)
     ≡⟨ subst-∘ (coh-frame (1+ n) p (1+ q) (1+ r) (↓₄ p≤r≤q≤n) ε ω D d) _ ⟩
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
        (subst-∘ (coh-frame (1+ n) p r p ((◆₄ (↓₃' drop₄-3 p≤r≤q≤n))) ω θ D d) _) ⟩
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
        (subst-∘ (coh-frame (1+ n) p (1+ q) p (◆₄ (↓₃ (drop₄-2 p≤r≤q≤n))) ε θ _ d) _) ⟩⁻¹
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

coh-painting n p q r {zero} (ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) ε ω D E d c
  with recover-nat-eq p r Hpr | recover-nat-eq δrq δpq Hprq | recover-nat-eq δrn δpn Hprn
... | refl | refl | refl = refl
coh-painting n p (1+ q) (1+ r) {1+ δ} p≤r≤q≤n@(ineq₄ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn)
   ε ω D E d (l , c) =
   let 1+p≤r≤q≤n = ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn in
   let rec = coh-painting n (1+ p) (1+ q) (1+ r) {δ} 1+p≤r≤q≤n ε ω D E (d , l) c in
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

opaque
  Ctx : (n : ℕ) → Type₁
  Ctx = νSet-<

  fullframe : {n : ℕ} (D : Ctx n) → HSet
  fullframe {n} D = frame n n (◆₂ n) D

  [] : Ctx 0
  [] = tt
  
  _∷_ : ∀ {n} → (D : Ctx n) → (fullframe D .Dom → HSet) → Ctx (1+ n)
  _∷_ D E = D , E

infixl 4 _∷_

TotalSpace : ∀ {n} → (D : Ctx n) → (fullframe D .Dom → HSet) → HSet
TotalSpace D E = HΣ[ d ∈ fullframe D ] E d

record νSet-> (n : ℕ) (D : Ctx n) : Type₁ where
  coinductive
  field
   this : fullframe D .Dom → HSet
   next : νSet-> (1+ n) (D ∷ this)

open νSet-> public

νSet : Type₁
νSet = νSet-> 0 []
