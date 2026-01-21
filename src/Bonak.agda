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
open HΠ fe fe-≡

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

frame : ∀ n p δ → .(Hp : δ + p ≡ n)
      → (D : νSet-< n)
      → HSet
        
layer : ∀ n p δ → .(Hp : 1+ δ + p ≡ n)
      → (D : νSet-< n)
      → (d : frame n p (1+ δ) Hp D .Dom)
      → HSet

painting : ∀ n p δ → .(Hp : δ + p ≡ n)
         → (D : νSet-< n) (E : νSet-= n D)
         → (d : frame n p δ Hp D .Dom)
         → HSet

restr-frame : ∀ n p q δ δ'
            → .(Hp : δ + p ≡ n) .(Hq : δ' + p ≡ q)
            → .(δ'≤δ : δ' ≤ δ) 
            → (ε : arity)
            → (D : νSet-< (1+ n))
            → (d : frame (1+ n) p (1+ δ) (⇑ Hp) D .Dom)
            → frame n p δ Hp (D .₁) .Dom

restr-layer : ∀ n p q δ δ'
            → .(Hp : 1+ δ + p ≡ n) .(Hq : δ' + p ≡ q)
            → .(δ'≤δ : δ' ≤ δ)
            → (ε : arity)
            → (D : νSet-< (1+ n))
            → (d : frame (1+ n) p (2+ δ) (⇑ Hp) D .Dom)
            → (l : layer (1+ n) p (1+ δ) (⇑ Hp) D d .Dom)
            → layer n p δ Hp (D .₁) (restr-frame n p (1+ q) (1+ δ) (1+ δ') Hp (⇑ Hq) (s≤s δ'≤δ) ε D d) .Dom

restr-painting : ∀ n p q δ δ'
               → .(Hp : δ + p ≡ n) .(Hq : δ' + p ≡ q)
               → .(δ'≤δ : δ' ≤ δ) 
               → (ε : arity)
               → (D : νSet-< (1+ n)) (E : νSet-= (1+ n) D)
               → (d : frame (1+ n) p (1+ δ) (⇑ Hp) D .Dom)
               → (c : painting (1+ n) p (1+ δ) (⇑ Hp) D E d .Dom)
               → painting n p δ Hp (D .₁) (D .₂)
                  (restr-frame n p q δ δ' Hp Hq δ'≤δ ε D d) .Dom

coh-frame : ∀ n p q r δ δ' δ''
          → .(Hp : δ + p ≡ n) .(Hq : δ' + p ≡ q) .(Hr : δ'' + p ≡ r)
          → .(δ''≤δ' : δ'' ≤ δ') .(δ'≤δ : δ' ≤ δ)
          → (ε ω : arity)
          → (D : νSet-< (2+ n))
          → (d : frame (2+ n) p (2+ δ) (⇑ ⇑ Hp) D .Dom)
          → restr-frame n p q δ δ' Hp Hq δ'≤δ ε (D .₁)
              (restr-frame (1+ n) p r (1+ δ) δ'' (⇑ Hp) Hr (↑ (δ''≤δ' ↕ δ'≤δ)) ω D d)
          ≡ restr-frame n p r δ δ'' Hp Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁)
              (restr-frame (1+ n) p (1+ q) (1+ δ) (1+ δ') (⇑ Hp) (⇑ Hq) (s≤s δ'≤δ) ε D d)

coh-layer : ∀ n p q r δ δ' δ''
          → .(Hp : 1+ δ + p ≡ n) .(Hq : δ' + p ≡ q) .(Hr : δ'' + p ≡ r)
          → .(δ''≤δ' : δ'' ≤ δ') .(δ'≤δ : δ' ≤ δ)
          → (ε ω : arity)
          → (D : νSet-< (2+ n))
          → (d : frame (2+ n) p (3+ δ) (⇑ ⇑ Hp) D .Dom)
          → (l : layer (2+ n) p (2+ δ) (⇑ ⇑ Hp) D d .Dom)
          → subst (λ - → layer n p δ _ (D .₁ .₁) - .Dom)
              (coh-frame n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') Hp (⇑ Hq) (⇑ Hr) (s≤s δ''≤δ') (s≤s δ'≤δ) ε ω D d)
              (restr-layer n p q δ δ' Hp Hq δ'≤δ ε (D .₁)
                (restr-frame (1+ n) p (1+ r) (2+ δ) (1+ δ'') (⇑ Hp) (⇑ Hr) (↑ s≤s (δ''≤δ' ↕ δ'≤δ)) ω D d)
                (restr-layer (1+ n) p r (1+ δ) δ'' (⇑ Hp) Hr (↑ (δ''≤δ' ↕ δ'≤δ)) ω D d l))
          ≡ restr-layer n p r δ δ'' Hp Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁)
              (restr-frame (1+ n) p (2+ q) (2+ δ) (2+ δ') (⇑ Hp) (⇑ ⇑ Hq) (s≤s (s≤s δ'≤δ)) ε D d)
              (restr-layer (1+ n) p (1+ q) (1+ δ) (1+ δ') (⇑ Hp) (⇑ Hq) (s≤s δ'≤δ) ε D d l)
           
coh-painting : ∀ n p q r δ δ' δ''
          → .(Hp : δ + p ≡ n) .(Hq : δ' + p ≡ q) .(Hr : δ'' + p ≡ r)
          → .(δ''≤δ' : δ'' ≤ δ') .(δ'≤δ : δ' ≤ δ)
          → (ε ω : arity)
          → (D : νSet-< (2+ n)) (E : νSet-= (2+ n) D)  
          → (d : frame (2+ n) p (2+ δ) (⇑ ⇑ Hp) D .Dom)
          → (c : painting (2+ n) p (2+ δ) (⇑ ⇑ Hp) D E d .Dom)
          → subst (λ - → painting n p δ _ (D .₁ .₁) (D .₁ .₂) - .Dom)
              (coh-frame n p q r δ δ' δ'' Hp Hq Hr δ''≤δ' δ'≤δ ε ω D d)
              (restr-painting n p q δ δ' Hp Hq δ'≤δ ε (D .₁) (D .₂)
                (restr-frame (1+ n) p r (1+ δ) δ'' (⇑ Hp) Hr (↑ (δ''≤δ' ↕ δ'≤δ)) ω D d)
                (restr-painting (1+ n) p r (1+ δ) δ'' (⇑ Hp) Hr (↑ (δ''≤δ' ↕ δ'≤δ)) ω D E d c))
          ≡ restr-painting n p r δ δ'' Hp Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁) (D .₂)
              (restr-frame (1+ n) p (1+ q) (1+ δ) (1+ δ') (⇑ Hp) (⇑ Hq) (s≤s δ'≤δ) ε D d)
              (restr-painting (1+ n) p (1+ q) (1+ δ) (1+ δ') (⇑ Hp) (⇑ Hq) (s≤s δ'≤δ) ε D E d c)

νSet-= n D = frame n n 0 refl D .Dom → HSet 

frame n zero   δ Hp D = HUnit
frame n (1+ p) δ Hp D = HΣ[ d ∈ frame n p (1+ δ) (← Hp) D ] layer n p δ (← Hp) D d

layer (1+ n) p δ Hp D d =
 HΠ[ ε ∈ arity ] painting n p δ (⇓ Hp) (D .₁) (D .₂) (restr-frame n p p δ 0 (⇓ Hp) refl 0≤n ε D d)

painting n p zero Hp D E d with recover-nat-eq Hp
... | refl = E d
painting n p (1+ δ) Hp D E d = HΣ[ l ∈ layer n p δ Hp D d ] painting n (1+ p) δ (⇒ Hp) D E (d , l)

restr-frame n zero   q δ δ' Hp Hq δ'≤δ ε D d = tt
restr-frame n (1+ p) zero δ zero Hp ()
restr-frame n (1+ p) zero δ (1+ δ') Hp ()
restr-frame n (1+ p) (1+ q) δ δ' Hp Hq δ'≤δ ε D (d , l) =
  restr-frame n p (1+ q) (1+ δ) (1+ δ') (← Hp) (← Hq) (s≤s δ'≤δ) ε D d ,
  restr-layer n p q δ δ' (← Hp) (⇓ ← Hq) δ'≤δ ε D d l

restr-layer (1+ n) p q δ δ' Hp Hq δ'≤δ ε (D , E) d l ω =
    subst (λ - → painting n p δ (⇓ Hp) (D .₁) (D .₂) - .Dom)
      (coh-frame n p q p δ δ' 0 (⇓ Hp) Hq refl 0≤n δ'≤δ ε ω (D , E) d)
      (restr-painting n p q δ δ' (⇓ Hp) Hq δ'≤δ ε D E
         (restr-frame (1+ n) p p (1+ δ) 0 Hp refl 0≤n ω (D , E) d) (l ω))  

restr-painting n p q δ 0 Hp Hq δ'≤δ ε D E d (l , c) with recover-nat-eq Hq
... | refl = l ε
restr-painting n p (1+ q) (1+ δ) (1+ δ') Hp Hq δ'≤δ ε D E d (l , c) =
  restr-layer n p q δ δ' Hp (⇓ Hq) (↓↓ δ'≤δ) ε D d l ,
  restr-painting n (1+ p) (1+ q) δ δ' (⇒ Hp) (⇒ Hq) (↓↓ δ'≤δ) ε D E (d , l) c

coh-frame n zero q r δ δ' δ'' Hp Hq Hr δ''≤δ' δ'≤δ ε ω D d = refl
coh-frame n (1+ p) zero r δ zero δ'' Hp ()
coh-frame n (1+ p) (1+ q) zero δ δ' zero Hp Hq ()
coh-frame n (1+ p) (1+ q) (1+ r) δ δ' δ'' Hp Hq Hr δ''≤δ' δ'≤δ ε ω D (d , l) =
  Σ-≡→≡ (coh-frame n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'')
             (← Hp) (← Hq) (← Hr) (s≤s δ''≤δ') (s≤s δ'≤δ) ε ω D d ,
         coh-layer n p q r δ δ' δ'' (← Hp) (⇓ (← Hq)) (⇓ (← Hr)) δ''≤δ' δ'≤δ ε ω D d l)

coh-layer (1+ n) p q r δ δ' δ'' Hp Hq Hr δ''≤δ' δ'≤δ ε ω D d l = fe _ _ (λ θ → I θ)
 where
  I : (θ : arity)
    → subst (λ - → layer (1+ n) p δ _ (D .₁ .₁) - .Dom)
        (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d)
        (restr-layer (1+ n) p q δ δ' _ _ _ ε (D .₁) _
          (restr-layer (2+ n) p r (1+ δ) δ'' _ _ _ ω D d l)) θ
    ≡ restr-layer (1+ n) p r δ δ'' _ _ _ ω (D .₁) _
        (restr-layer (2+ n) p (1+ q) (1+ δ) (1+ δ') _ _ _ ε D d l) θ
  I θ =
    subst (λ - → layer (1+ n) p δ _ (D .₁ .₁) - .Dom)
      (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d)
      (restr-layer (1+ n) p q δ δ' _ _ _ ε (D .₁) _
        (restr-layer (2+ n) p r (1+ δ) δ'' _ _ _ ω D d l)) θ
      ≡⟨ subst-application (λ - → (layer (1+ n) p δ _ _ -) .Dom) (λ -₁ -₂ → -₂ θ)
           (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d) ⟩⁻¹
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂)
                   (restr-frame n p p δ 0 _ _ _ θ (D .₁ .₁) -) .Dom)
      (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d) (
    restr-layer (1+ n) p q δ δ' Hp Hq δ'≤δ ε (D .₁) _
      (restr-layer (2+ n) p r (1+ δ) δ'' _ Hr (↑ (δ''≤δ' ↕ δ'≤δ)) ω D d l) θ)
      ≡⟨ subst-∘ (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d) ⟩
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (cong (restr-frame n p p δ 0 _ _ _ θ (D .₁ .₁)) 
        (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (coh-frame n p q p δ δ' 0 _ _ _ _ _ ε θ (D .₁)
        (restr-frame (2+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d)) (
    restr-painting n p q δ δ' _ _ _ ε (D .₁ .₁) (D .₁ .₂) _
      (restr-layer (2+ n) p r (1+ δ) δ'' _ Hr (↑ (δ''≤δ' ↕ δ'≤δ)) ω D d l θ)))
      ≡⟨ cong (λ - →
           subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
             (cong (restr-frame n p p δ 0 _ _ _ θ (D .₁ .₁)) 
                (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d)) (
           subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
             (coh-frame n p q p δ δ' 0 _ _ _ _ _ ε θ (D .₁)
               (restr-frame (2+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d)) -))
         (subst-application _
            (restr-painting n p q δ δ' _ _ _ ε (D .₁ .₁) (D .₁ .₂))
            (coh-frame (1+ n) p r p (1+ δ) δ'' 0 _ _ _ _ _ ω θ D d)) ⟩⁻¹
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (cong (restr-frame n p p δ 0 _ _ _ θ (D .₁ .₁)) 
        (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (coh-frame n p q p δ δ' 0 _ _ _ _ _ ε θ (D .₁)
        (restr-frame (2+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂)
                   (restr-frame n p q δ δ' _ _ _ ε (D .₁ .₁) -) .Dom)
      (coh-frame (1+ n) p r p (1+ δ) δ'' 0 _ _ _ _ _ ω θ D d) (
    restr-painting n p q δ δ' _ _ _ ε (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p r (1+ δ) δ'' _ _ _ ω (D .₁) (D .₂) _ (l θ)))))
      ≡⟨ cong (λ - →
           subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
             (cong (restr-frame n p p δ 0 _ _ _ θ (D .₁ .₁)) 
                (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d)) (
           subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
             (coh-frame n p q p δ δ' 0 _ _ _ _ _ ε θ (D .₁)
               (restr-frame (2+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d)) -))
          (subst-∘ (coh-frame (1+ n) p r p (1+ δ) δ'' 0 _ _ _ _ _ ω θ D d)) ⟩
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (cong (restr-frame n p p δ 0 _ _ _ θ (D .₁ .₁)) 
        (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (coh-frame n p q p δ δ' 0 _ _ _ _ _ ε θ (D .₁)
        (restr-frame (2+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
      (cong (restr-frame n p q δ δ' _ _ _ ε (D .₁ .₁))
        (coh-frame (1+ n) p r p (1+ δ) δ'' 0 _ _ _ 0≤n _ ω θ D d)) (
    restr-painting n p q δ δ' _ _ _ ε (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p r (1+ δ) δ'' _ _ _ ω (D .₁) (D .₂) _ (l θ)))))
      ≡⟨ coh₂ {A = frame n p δ _ (D .₁ .₁ .₁)}
              (cong (restr-frame n p p δ 0 _ _ _ θ (D .₁ .₁)) 
                (coh-frame (1+ n) p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ (s≤s δ''≤δ') _ ε ω D d))
              (coh-frame n p q p δ δ' 0 _ _ _ _ _ ε θ (D .₁)
                (restr-frame (2+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d))
              (cong (restr-frame n p q δ δ' _ _ _ ε (D .₁ .₁))
                (coh-frame (1+ n) p r p (1+ δ) δ'' 0 _ _ _ _ _ ω θ D d))
              (coh-frame n p r p δ δ'' 0 _ _ _ 0≤n _ ω θ (D .₁ .₁ , D .₁ .₂)
                (restr-frame (2+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d))
              (cong (restr-frame n p r δ δ'' _ Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁ .₁))
                (coh-frame (1+ n) p (1+ q) p (1+ δ) (1+ δ') 0 _ (⇑ Hq) _ 0≤n (s≤s δ'≤δ) ε θ _ d))
              (coh-frame n p q r δ δ' δ'' _ _ _ _ _ ε ω (D .₁)
                (restr-frame (2+ n) p p (2+ δ) 0 _ _ _ θ D d)) ⟩
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
       (coh-frame n p r p δ δ'' 0 _ _ _ 0≤n _ ω θ (D .₁ .₁ , D .₁ .₂)
         (restr-frame (2+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
       (cong (restr-frame n p r δ δ'' _ Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁ .₁))
         (coh-frame (1+ n) p (1+ q) p (1+ δ) (1+ δ') 0 _ (⇑ Hq) _ 0≤n (s≤s δ'≤δ) ε θ _ d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
       (coh-frame n p q r δ δ' δ'' _ _ _ δ''≤δ' _ ε ω (D .₁)
         (restr-frame (2+ n) p p (2+ δ) 0 _ _ _ θ D d)) (
    restr-painting n p q δ δ' _ _ _ ε (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p r (1+ δ) δ'' _ _ _ ω (D .₁) (D .₂) _ (l θ)))))
      ≡⟨ cong (λ - →
           subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
             (coh-frame n p r p δ δ'' 0 _ _ _ 0≤n _ ω θ (D .₁ .₁ , D .₁ .₂)
               (restr-frame (2+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)) (
           subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
             (cong (restr-frame n p r δ δ'' _ Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁ .₁))
             (coh-frame (1+ n) p (1+ q) p (1+ δ) (1+ δ') 0 _ (⇑ Hq) _ 0≤n (s≤s δ'≤δ) ε θ _ d)) -))
        (coh-painting n p q r δ δ' δ'' _ _ _ _ _ ε ω (D .₁) (D .₂) _ (l θ)) ⟩
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
       (coh-frame n p r p δ δ'' 0 _ _ _ 0≤n _ ω θ (D .₁ .₁ , D .₁ .₂)
         (restr-frame (2+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
       (cong (restr-frame n p r δ δ'' _ Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁ .₁))
         (coh-frame (1+ n) p (1+ q) p (1+ δ) (1+ δ') 0 _ (⇑ Hq) _ 0≤n (s≤s δ'≤δ) ε θ _ d)) (
    restr-painting n p r δ δ'' _ _ _ ω (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p (1+ q) (1+ δ) (1+ δ') _ _ _ ε (D .₁) (D .₂) _ (l θ))))
      ≡⟨ cong (subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                 (coh-frame n p r p δ δ'' 0 _ _ _ 0≤n _ ω θ (D .₁ .₁ , D .₁ .₂)
                 (restr-frame (2+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)))
           (subst-∘ (coh-frame (1+ n) p (1+ q) p (1+ δ) (1+ δ') 0 _ (⇑ Hq) _ 0≤n (s≤s δ'≤δ) ε θ _ d)) ⟩⁻¹
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
       (coh-frame n p r p δ δ'' 0 _ _ _ 0≤n _ ω θ (D .₁ .₁ , D .₁ .₂)
         (restr-frame (2+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)) (
    subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂)
                   (restr-frame n p r δ δ'' _ Hr (δ''≤δ' ↕ δ'≤δ) ω (D .₁ .₁) -) .Dom)
       (coh-frame (1+ n) p (1+ q) p (1+ δ) (1+ δ') 0 _ (⇑ Hq) _ 0≤n (s≤s δ'≤δ) ε θ _ d) (
    restr-painting n p r δ δ'' _ _ _ ω (D .₁ .₁) (D .₁ .₂) _
      (restr-painting (1+ n) p (1+ q) (1+ δ) (1+ δ') _ _ _ ε (D .₁) (D .₂) _ (l θ))))
      ≡⟨ cong (subst (λ - → painting n p δ _ (D .₁ .₁ .₁) (D .₁ .₁ .₂) - .Dom)
                     (coh-frame n p r p δ δ'' 0 _ _ _ 0≤n _ ω θ (D .₁ .₁ , D .₁ .₂)
                       (restr-frame (2+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)))
           (subst-application _ (restr-painting n p r δ δ'' _ _ _ ω (D .₁ .₁) (D .₁ .₂))
             (coh-frame (1+ n) p (1+ q) p (1+ δ) (1+ δ') 0 _ (⇑ Hq) _ 0≤n (s≤s δ'≤δ) ε θ _ d)) ⟩ 
    restr-layer (1+ n) p r δ δ'' _ _ _ ω (D .₁) _
        (restr-layer (2+ n) p (1+ q) (1+ δ) (1+ δ') _ _ _ ε D d l) θ ∎

coh-painting n p q r δ δ' zero Hp Hq Hr δ''≤δ' δ'≤δ ε ω D E d c with recover-nat-eq Hr
... | refl = refl
coh-painting n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'')
  Hp Hq Hr δ''≤δ' δ'≤δ ε ω D E d (l , c) =
  subst (λ - → painting n p (1+ δ) _ (D .₁ .₁) (D .₁ .₂) - .Dom)
    (coh-frame n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d)
    (restr-painting n p (1+ q) (1+ δ) (1+ δ') _ _ _ ε (D .₁) (D .₂)
     (restr-frame (1+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d)
     (restr-painting (1+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D E d (l , c)))
    ≡⟨ subst-Σ (coh-frame n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d) ⟩
  subst (λ - → layer n p δ Hp (D .₁ .₁) - .Dom)
   (coh-frame n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d)
   (restr-layer n p q δ δ' _ _ _ ε (D .₁)
     (restr-frame (1+ n) p (1+ r) (2+ δ) (1+ δ'') _ _ _ ω D d)
     (restr-layer (1+ n) p r (1+ δ) δ'' _ _ _ ω D d l )) ,
  subst (λ - → painting n (1+ p) δ (⇒ Hp) (D .₁ .₁) (D .₁ .₂) - .Dom)
   (Σ-≡→≡ (coh-frame n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d , refl))
   (restr-painting n (1+ p) (1+ q) δ δ' _ _ _ ε (D .₁) (D .₂)
     (restr-frame    (1+ n) (1+ p) (1+ r) (1+ δ) δ'' (⇑ ⇒ Hp) (⇒ Hr) _ ω D (d , l))
     (restr-painting (1+ n) (1+ p) (1+ r) (1+ δ) δ'' _ _ _ ω D E (d , l) c))
    ≡⟨ Σ-≡→≡ ( coh-layer n p q r δ δ' δ'' Hp (⇓ Hq) (⇓ Hr) (↓↓ δ''≤δ') (↓↓ δ'≤δ) ε ω _ d l
             , subst-Σ' (coh-frame n p (1+ q) (1+ r) (1+ δ) (1+ δ') (1+ δ'') _ _ _ _ _ ε ω D d)
                        (coh-layer n p q r δ δ' δ'' Hp (⇓ Hq) (⇓ Hr) (↓↓ δ''≤δ') (↓↓ δ'≤δ) ε ω _ d l)) ⟩
  restr-layer n p r δ δ'' _ _ _ ω (D .₁)
    (restr-frame (1+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)
    (restr-layer (1+ n) p (1+ q) (1+ δ) (1+ δ') _ _ _ ε D d l) ,
  subst (λ - → painting n (1+ p) δ (⇒ Hp) (D .₁ .₁) (D .₁ .₂) - .Dom)
   (coh-frame n (1+ p) (1+ q) (1+ r) δ δ' δ'' (⇒ Hp) (⇒ Hq) (⇒ Hr) _ _ ε ω D (d , l))
   (restr-painting n (1+ p) (1+ q) δ δ' _ _ _ ε (D .₁) (D .₂)
     (restr-frame    (1+ n) (1+ p) (1+ r) (1+ δ) δ'' (⇑ ⇒ Hp) (⇒ Hr) _ ω D (d , l))
     (restr-painting (1+ n) (1+ p) (1+ r) (1+ δ) δ'' _ _ _ ω D E (d , l) c))
    ≡⟨ Σ-≡→≡ (refl , coh-painting n (1+ p) (1+ q) (1+ r) δ δ' δ''
         (⇒ Hp) (⇒ Hq) (⇒ Hr) (↓↓ δ''≤δ') (↓↓ δ'≤δ) ε ω D E (d , l) c) ⟩
  restr-painting n p (1+ r) (1+ δ) (1+ δ'') _ _ _ ω (D .₁) (D .₂)
    (restr-frame (1+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D d)
    (restr-painting (1+ n) p (2+ q) (2+ δ) (2+ δ') _ _ _ ε D E d (l , c)) ∎

record νSet-> (n : ℕ) (D : νSet-< n) : Type₁ where
 coinductive
 field
   this : νSet-= n D
   next : νSet-> (1+ n) (D , this)
