{-# OPTIONS --termination-depth=3 #-}

open import Prelude

module νSet.Equiv
  (fe : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
      → (f g : (a : A) → B a)
      → (∀ a → f a ≡ g a)
      → f ≡ g)
  (fe-≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
        → (f g : (a : A) → B a)
        → (p : f ≡ g)
        → fe f g (λ a → cong-app p a) ≡ p)
  (arity : Type)
 where

open import Inequalities
open import HSet
open import Equiv
open HΠ fe fe-≡
open ≃Π fe

open import νSet.Base fe fe-≡ arity

νSet-≃ : (n : ℕ) (D D' : νSet-< n) → Type₁

νSet-≃-frame : ∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
             → {D D' : νSet-< n}
             → νSet-≃ n D D'
             → frame n p p≤n D .Dom ≃ frame n p p≤n D' .Dom

νSet-≃-layer : ∀ n p {δ} → (p≤n : [ 1+ p ≤ n ][ δ ]₂)
             → {D D' : νSet-< n}
             → (D-≈ : νSet-≃ n D D')
             → (d : frame n p (↓₂ p≤n) D .Dom)
             → layer n p p≤n D d .Dom
             ≃ layer n p p≤n D' (νSet-≃-frame n p (↓₂ p≤n) D-≈ .₁ d) .Dom

νSet-≃-painting : ∀ n p {δ} → (p≤n : [ p ≤ n ][ δ ]₂)
                → {D D' : νSet-< n} {E : νSet-= n D} {E' : νSet-= n D'}
                → (D-≈ : νSet-≃ n D D')
                → (E-≈ : ∀ d → E d .Dom ≃ E' (νSet-≃-frame n n (◆₂ n) D-≈ .₁ d) .Dom)
                → (d : frame n p p≤n D .Dom)
                → painting n p p≤n D E d .Dom
                ≃ painting n p p≤n D' E' (νSet-≃-frame n p p≤n D-≈ .₁ d) .Dom

νSet-≃ zero D D'   = ⊤
νSet-≃ (1+ n) (D , E) (D' , E') =
  Σ[ D-≃ ∈ νSet-≃ n D D' ]
    (∀ d → (E d .Dom) ≃ (E' (νSet-≃-frame n n (◆₂ n) D-≃ .₁ d) .Dom))

νSet-≃-restr-frame : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
                   → (ε : arity)
                   → {D D' : νSet-< (1+ n)}
                   → (D-≃ : νSet-≃ (1+ n) D D')
                   → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
                   → νSet-≃-frame n p (drop₃-2 p≤q≤n) (D-≃ .₁)  .₁
                       (restr-frame n p q p≤q≤n ε D d)
                   ≡ restr-frame n p q p≤q≤n ε D'
                       (νSet-≃-frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ .₁ d)
                       
νSet-≃-restr-layer : ∀ n p q {δ} → (p≤q≤n : [ 1+ p ≤ 1+ q ≤ n ][ δ ]₃)
                   → (ε : arity)
                   → {D D' : νSet-< (1+ n)}
                   → (D-≃ : νSet-≃ (1+ n) D D')
                   → (d : frame (1+ n) p (↓₂ ↑₂ drop₃-2 p≤q≤n) D .Dom)
                   → (l : layer (1+ n) p (↑₂ drop₃-2 p≤q≤n) D d .Dom)
                   → subst (λ d → layer n p (drop₃-2 p≤q≤n) (D' .₁) d .Dom)
                       (νSet-≃-restr-frame n p (1+ q) _ ε D-≃ d)
                       (νSet-≃-layer n p (drop₃-2 p≤q≤n) (D-≃ .₁)
                         (restr-frame n p (1+ q) (↓₃ p≤q≤n) ε D d) .₁
                         (restr-layer n p q p≤q≤n ε D d l))
                   ≡ restr-layer n p q p≤q≤n ε D'
                       (νSet-≃-frame (1+ n) p (↓₂ ↑₂ drop₃-2 p≤q≤n) D-≃ .₁ d)
                       (νSet-≃-layer (1+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ d .₁ l)

νSet-≃-restr-painting : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
                      → (ε : arity)
                      → {D D' : νSet-< (1+ n)} {E : νSet-= _ D} {E' : νSet-= _ D'}
                      → (D-≃ : νSet-≃ (1+ n) D D')
                      → (E-≃ : ∀ d → E d .Dom ≃ E' (νSet-≃-frame (1+ n) (1+ n) (◆₂ (1+ n)) D-≃ .₁ d) .Dom) 
                      → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
                      → (c : painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D E d .Dom)
                      → subst (λ d → painting n p (drop₃-2 p≤q≤n) (D' .₁) (D' .₂) d .Dom)
                         (νSet-≃-restr-frame n p q _ ε D-≃ d)
                         (νSet-≃-painting n p (drop₃-2 p≤q≤n) (D-≃ .₁) (D-≃ .₂)
                           (restr-frame n p q p≤q≤n ε D d) .₁
                           (restr-painting n p q p≤q≤n ε D E d c))
                      ≡ restr-painting n p q p≤q≤n ε D' E'
                          (νSet-≃-frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ .₁ d)
                          (νSet-≃-painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ E-≃ d .₁ c) 

νSet-≃-frame n zero p≤n D-≃ = ≃id _
νSet-≃-frame n (1+ p) p≤n D-≃ =
  Σ-≃ (νSet-≃-frame n p (↓₂ p≤n) D-≃) (λ d → νSet-≃-layer n p p≤n _ d)
  
νSet-≃-layer (1+ n) p p≤n {D} {D'} (D-≃ , E-≃) d =
  Π-≃-snd λ ε → (νSet-≃-painting n p (⇓₂ p≤n) D-≃ E-≃ (restr-frame n p p (◆₃ (⇓₂ p≤n)) ε _ d))
             ∙≃ eq→isEquiv (cong (λ - → painting n p _ (D' .₁) (D' .₂) - .Dom)
                  (νSet-≃-restr-frame n p p _ ε (D-≃ , E-≃) d))

νSet-≃-painting n p {zero} (ineq₂ Hpn) D-≃ E-≃ d
  with recover-nat-eq' p n Hpn
... | refl = E-≃ d
νSet-≃-painting n p {1+ δ} (ineq₂ Hpn) D-≃ E-≃ d =
   Σ-≃ (νSet-≃-layer n p (ineq₂ Hpn) _ d)
       (λ l → νSet-≃-painting n (1+ p) _ D-≃ E-≃ (d , l))


νSet-≃-restr-frame n zero q p≤q≤n ε D-≃ d = refl
νSet-≃-restr-frame n (1+ p) (1+ q) p≤q≤n ε {D} D-≃ (d , l) =
  Σ-≡→≡ ( νSet-≃-restr-frame n p (1+ q) _ ε {D} D-≃ d
        , νSet-≃-restr-layer n p q p≤q≤n ε D-≃ d l )

νSet-≃-restr-layer (1+ n) p q p≤q≤n ε {D} {D'} D-≃ d l = fe _ _ helper
 where
 helper : (ω : arity)
        → subst (λ d → layer (1+ n) p (drop₃-2 p≤q≤n) (D' .₁) d .Dom)
            (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d)
            (νSet-≃-layer (1+ n) p (drop₃-2 p≤q≤n) (D-≃ .₁)
              (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d) .₁
              (restr-layer (1+ n) p q p≤q≤n ε D d l)) ω
        ≡ restr-layer (1+ n) p q p≤q≤n ε D'
            (νSet-≃-frame (2+ n) p (↓₂ ↑₂ drop₃-2 p≤q≤n) D-≃ .₁ d)
            (νSet-≃-layer (2+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ d .₁ l) ω
 helper ω =
   subst (λ d → layer (1+ n) p (drop₃-2 p≤q≤n) (D' .₁) d .Dom)
     (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d)
     (νSet-≃-layer (1+ n) p (drop₃-2 p≤q≤n) (D-≃ .₁)
       (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d) .₁
       (restr-layer (1+ n) p q p≤q≤n ε D d l)) ω
     ≡⟨ subst-application (λ - → layer (1+ n) p (drop₃-2 p≤q≤n) _ - .Dom) (λ -₁ -₂ → -₂ ω)
          (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) ⟩⁻¹
   subst (λ - → painting n p _ _ _ (restr-frame n p p _ ω _ -) .Dom)
     (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) (
   subst id (cong (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
     (νSet-≃-restr-frame n p p _ ω (D-≃ .₁) (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d))) 
     (νSet-≃-painting n p _ (D-≃ .₁ .₁) (D-≃ .₁ .₂)
       (restr-frame n p p _ ω _ (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d)) .₁
       (subst (λ - → painting n p _ (D .₁ .₁) (D .₁ .₂)  - .Dom)
         (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d)
         (restr-painting n p q (⇓₃ p≤q≤n) ε (D .₁) (D .₂) _ (l ω)))))
     ≡⟨ cong (subst (λ - → painting n p _ _ _ (restr-frame n p p _ ω _ -) .Dom)
                (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d))
             (subst-∘ (νSet-≃-restr-frame n p p _ ω (D-≃ .₁)
                         (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d))) ⟩⁻¹
   subst (λ - → painting n p _ _ _ (restr-frame n p p _ ω _ -) .Dom)
     (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) (
   subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
     (νSet-≃-restr-frame n p p _ ω (D-≃ .₁) (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d))
     (νSet-≃-painting n p _ (D-≃ .₁ .₁) (D-≃ .₁ .₂)
       (restr-frame n p p _ ω _ (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d)) .₁
       (subst (λ - → painting n p _ (D .₁ .₁) (D .₁ .₂)  - .Dom)
         (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d)
         (restr-painting n p q (⇓₃ p≤q≤n) ε (D .₁) (D .₂) _ (l ω)))))
     ≡⟨ cong (λ - → subst (λ - → painting n p _ _ _ (restr-frame n p p _ ω _ -) .Dom)
                      (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) (
                    subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
                      (νSet-≃-restr-frame n p p _ ω (D-≃ .₁)
                        (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d)) -))
          (subst-application _
             (λ -₁ -₂ → νSet-≃-painting n p _ (D-≃ .₁ .₁) (D-≃ .₁ .₂) -₁ .₁ -₂)
             (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d)) ⟩⁻¹
   subst (λ - → painting n p _ _ _ (restr-frame n p p _ ω _ -) .Dom)
     (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) (
   subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
     (νSet-≃-restr-frame n p p _ ω (D-≃ .₁) (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d)) (
   subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) (νSet-≃-frame n p _ (D-≃ .₁ .₁) .₁ -) .Dom)
     (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d) 
     (νSet-≃-painting n p _ (D-≃ .₁ .₁) (D-≃ .₁ .₂)
       (restr-frame n p q _ ε _ (restr-frame (1+ n) p p _ ω D d)) .₁
       (restr-painting n p q (⇓₃ p≤q≤n) ε (D .₁) (D .₂) _ (l ω)))))
     ≡⟨ cong (λ - → subst (λ - → painting n p _ _ _ (restr-frame n p p _ ω _ -) .Dom)
                      (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) (
                    subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
                      (νSet-≃-restr-frame n p p _ ω (D-≃ .₁)
                        (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d)) -))
          (subst-∘ (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d)) ⟩ 
   subst (λ - → painting n p _ _ _ (restr-frame n p p _ ω _ -) .Dom)
     (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) (
   subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
     (νSet-≃-restr-frame n p p _ ω (D-≃ .₁) (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d)) (
   subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
     (cong (νSet-≃-frame n p _ (D-≃ .₁ .₁) .₁)
        (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d)) 
     (νSet-≃-painting n p _ (D-≃ .₁ .₁) (D-≃ .₁ .₂)
       (restr-frame n p q _ ε _ (restr-frame (1+ n) p p _ ω D d)) .₁
       (restr-painting n p q (⇓₃ p≤q≤n) ε (D .₁) (D .₂) _ (l ω)))))
     ≡⟨ subst-∘ (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d) ⟩
   subst (λ - → painting n p _ _ _ - .Dom)
     (cong (restr-frame n p p _ ω _) (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d)) (
   subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
     (νSet-≃-restr-frame n p p _ ω (D-≃ .₁) (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d)) (
   subst (λ - → painting n p _ (D' .₁ .₁) (D' .₁ .₂) - .Dom)
     (cong (νSet-≃-frame n p _ (D-≃ .₁ .₁) .₁)
        (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d)) 
     (νSet-≃-painting n p _ (D-≃ .₁ .₁) (D-≃ .₁ .₂)
       (restr-frame n p q _ ε _ (restr-frame (1+ n) p p _ ω D d)) .₁
       (restr-painting n p q (⇓₃ p≤q≤n) ε (D .₁) (D .₂) _ (l ω)))))
     ≡⟨ coh₂ {A = frame n p _ (D' .₁ .₁) }
             (cong (restr-frame n p p _ ω _) (νSet-≃-restr-frame (1+ n) p (1+ q) _ ε D-≃ d))
             (νSet-≃-restr-frame n p p _ ω (D-≃ .₁) (restr-frame (1+ n) p (1+ q) (↓₃ p≤q≤n) ε D d))
             (cong (νSet-≃-frame n p _ (D-≃ .₁ .₁) .₁) (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D .₁ , D .₂) d))
             (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂) (νSet-≃-frame (2+ n) p _ D-≃ .₁ d))
             (cong (restr-frame n p q (⇓₃ p≤q≤n) ε (D' .₁)) (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d))
             (νSet-≃-restr-frame n p q _ ε (D-≃ .₁) (restr-frame (1+ n) p p _ ω D d)) ⟩
   subst (λ - → painting n p _ _ _ - .Dom)
     (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
       (νSet-≃-frame (2+ n) p _ D-≃ .₁ d)) (
   subst (λ - → painting n p _ _ _ - .Dom)
     (cong (restr-frame n p q (⇓₃ p≤q≤n) ε (D' .₁))
       (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)) (
   subst (λ - → painting n p _ _ _ - .Dom)
     (νSet-≃-restr-frame n p q _ ε (D-≃ .₁) (restr-frame (1+ n) p p _ ω D d)) (
     (νSet-≃-painting n p _ (D-≃ .₁ .₁) (D-≃ .₁ .₂)
       (restr-frame n p q _ ε _ (restr-frame (1+ n) p p _ ω D d)) .₁
       (restr-painting n p q (⇓₃ p≤q≤n) ε (D .₁) (D .₂) _ (l ω))))))
     ≡⟨ cong (λ - → subst (λ - → painting n p _ _ _ - .Dom)
                      (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
                        (νSet-≃-frame (2+ n) p _ D-≃ .₁ d)) (
                    subst (λ - → painting n p _ _ _ - .Dom)
                      (cong (restr-frame n p q (⇓₃ p≤q≤n) ε (D' .₁))
                         (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)) -))
             (νSet-≃-restr-painting n p q (⇓₃ p≤q≤n) ε (D-≃ .₁) (D-≃ .₂) _ (l ω)) ⟩
   subst (λ - → painting n p _ _ _ - .Dom)
     (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
       (νSet-≃-frame (2+ n) p _ D-≃ .₁ d)) (
   subst (λ - → painting n p _ _ _ - .Dom)
     (cong (restr-frame n p q (⇓₃ p≤q≤n) ε (D' .₁))
       (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)) (
     (restr-painting n p q (⇓₃ p≤q≤n) ε (D' .₁) (D' .₂) _
       (νSet-≃-painting (1+ n) p _ (D-≃ .₁) (D-≃ .₂)
          (restr-frame (1+ n) p p  _ ω D d) .₁ (l ω)))))
     ≡⟨ cong (subst (λ - → painting n p _ _ _ - .Dom)
               (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
                  (νSet-≃-frame (2+ n) p _ D-≃ .₁ d)))
             (subst-∘ (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)) ⟩⁻¹
   subst (λ - → painting n p _ _ _ - .Dom)
     (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
       (νSet-≃-frame (2+ n) p _ D-≃ .₁ d)) (
   subst (λ - → painting n p _ _ _ (restr-frame n p q (⇓₃ p≤q≤n) ε (D' .₁) -) .Dom)
     (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)
     (restr-painting n p q (⇓₃ p≤q≤n) ε (D' .₁) (D' .₂) _
       (νSet-≃-painting (1+ n) p _ (D-≃ .₁) (D-≃ .₂)
          (restr-frame (1+ n) p p  _ ω D d) .₁ (l ω))))
     ≡⟨ cong (subst (λ - → painting n p _ _ _ - .Dom)
                 (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
                   (νSet-≃-frame (2+ n) p _ D-≃ .₁ d))) 
         (subst-application (λ - → painting (1+ n) p _ (D' .₁) (D' .₂) - .Dom)
           (restr-painting n p q (⇓₃ p≤q≤n) ε (D' .₁) (D' .₂))
           (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)) ⟩
   subst (λ - → painting n p _ _ _ - .Dom)
     (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
       (νSet-≃-frame (2+ n) p _ D-≃ .₁ d)) (
   restr-painting n p q (⇓₃ p≤q≤n) ε (D' .₁) (D' .₂) _
     (subst (λ - → painting (1+ n) p _ (D' .₁) (D' .₂) - .Dom)
       (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)
       (νSet-≃-painting (1+ n) p _ (D-≃ .₁) (D-≃ .₂)
          (restr-frame (1+ n) p p  _ ω D d) .₁ (l ω))))
     ≡⟨ cong (λ - → subst (λ - → painting n p _ _ _ - .Dom)
                        (coh-frame n p q p (◆₄ (⇓₃ p≤q≤n)) ε ω (D' .₁ , D' .₂)
                        (νSet-≃-frame (2+ n) p _ D-≃ .₁ d)) (
                    restr-painting n p q (⇓₃ p≤q≤n) ε (D' .₁) (D' .₂) _ -))
        (subst-∘ (νSet-≃-restr-frame (1+ n) p p _ ω D-≃ d)) ⟩
   restr-layer (1+ n) p q p≤q≤n ε D'
      (νSet-≃-frame (2+ n) p (↓₂ ↑₂ drop₃-2 p≤q≤n) D-≃ .₁ d)
      (νSet-≃-layer (2+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ d .₁ l) ω ∎

νSet-≃-restr-painting n p q {zero} q≤q≤n@(ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) ε D-≃ E-≃ d (l , c)
  with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
... | refl | refl = subst-∘ (νSet-≃-restr-frame n q q q≤q≤n ε D-≃ d) 
νSet-≃-restr-painting n p (1+ q) {1+ δ} p≤q≤n@(ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) ε
 {D} {D'} {E} {E'} D-≃ E-≃  d (l , c) =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  let rec = νSet-≃-restr-painting n (1+ p) (1+ q) 1+p≤q≤n ε D-≃ E-≃ (d , l) c in
  subst (λ - → painting n p (drop₃-2 p≤q≤n) (D' .₁) (D' .₂) - .Dom)
    (νSet-≃-restr-frame n p (1+ q) p≤q≤n ε D-≃ d)
    (νSet-≃-painting n p (drop₃-2 p≤q≤n) (D-≃ .₁) (D-≃ .₂)
      (restr-frame n p (1+ q) p≤q≤n ε D d) .₁
      (restr-painting n p (1+ q) p≤q≤n ε D E d (l , c)))
    ≡⟨  subst-Σ (νSet-≃-restr-frame n p (1+ q) p≤q≤n ε D-≃ d) ⟩
  (subst (λ - → layer n p (drop₃-2 1+p≤q≤n) (D' .₁) - .Dom)
    (νSet-≃-restr-frame n p (1+ q) p≤q≤n ε D-≃ d)
    (νSet-≃-layer n p (drop₃-2 1+p≤q≤n) (D-≃ .₁)
      (restr-frame n p (1+ q) p≤q≤n ε D d) .₁
      (restr-layer n p q 1+p≤q≤n ε D d l))) ,
   (subst (λ - → painting n (1+ p) (drop₃-2 1+p≤q≤n) (D' .₁) (D' .₂) - .Dom)
     (Σ-≡→≡ (νSet-≃-restr-frame n p (1+ q) p≤q≤n ε D-≃ d , refl))
     (νSet-≃-painting n (1+ p) (drop₃-2 1+p≤q≤n) (D-≃ .₁) (D-≃ .₂)
      (restr-frame n p (1+ q) p≤q≤n ε D d , restr-layer n p q 1+p≤q≤n ε D d l) .₁
      (restr-painting n (1+ p) (1+ q) 1+p≤q≤n ε D E (d , l) c)))
    ≡⟨  Σ-≡→≡ (νSet-≃-restr-layer n p q 1+p≤q≤n ε D-≃ d l
             , (subst-Σ' (νSet-≃-restr-frame n p (1+ q) p≤q≤n ε D-≃ d)
               (νSet-≃-restr-layer n p q 1+p≤q≤n ε D-≃ d l))) ⟩
  (restr-layer n p q 1+p≤q≤n ε D'
    (νSet-≃-frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ .₁ d)
    (νSet-≃-layer (1+ n) p (↑₂ drop₃-2 1+p≤q≤n) D-≃ d .₁ l)) ,
   subst (λ - → painting n (1+ p) (drop₃-2 1+p≤q≤n) (D' .₁) (D' .₂) - .Dom)
    (νSet-≃-restr-frame n (1+ p) (1+ q) 1+p≤q≤n ε D-≃ (d , l))
    (νSet-≃-painting n (1+ p) (drop₃-2 1+p≤q≤n) (D-≃ .₁) (D-≃ .₂)
      (restr-frame n (1+ p) (1+ q) 1+p≤q≤n ε D (d , l)) .₁
      (restr-painting n (1+ p) (1+ q) 1+p≤q≤n ε D E (d , l) c))
    ≡⟨ Σ-≡→≡ (refl , rec ) ⟩
  restr-painting n p (1+ q) p≤q≤n ε D' E'
    (νSet-≃-frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ .₁ d)
    (νSet-≃-painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D-≃ E-≃ d .₁ (l , c)) ∎
