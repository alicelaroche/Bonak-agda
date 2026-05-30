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
  Face-≤ m (F0s , F0)× (∀ p {δ} → [ p ≤ m ][ δ ]₂ → arity → F0' .Dom → F0 .Dom)

record Presheaf-zipper (m : ℕ) : Type₁ where
  field
   |F0-<| : F0-< m
   |F0-≥| : ∀ n → HSet
   |Face-≤| : Face-≤ m (|F0-<| , |F0-≥| 0)
   |Face->| : ∀ n p {δ}
            → [ p ≤ n + m ][ δ ]₂ → arity
            → |F0-≥| (1+ n) .Dom
            → |F0-≥| n .Dom
open Presheaf-zipper

bump-zipper : ∀ m → Presheaf-zipper m → Presheaf-zipper (1+ m)
bump-zipper m zipper .|F0-<| = zipper .|F0-<| , zipper .|F0-≥| 0
bump-zipper m zipper .|F0-≥| = zipper .|F0-≥| ∘ suc
bump-zipper m zipper .|Face-≤| = zipper .|Face-≤| , zipper .|Face->| 0
bump-zipper m zipper .|Face->| = zipper .|Face->| ∘ suc

psh→zipper : Presheaf → Presheaf-zipper 0
psh→zipper psh .|F0-<| = tt
psh→zipper psh .|F0-≥| = psh .F0
psh→zipper psh .|Face-≤| = tt
psh→zipper psh .|Face->| = psh .Face

Presheaf-νSet-< : ∀ m → (F0 : F0-< (1+ m)) → (Face : Face-≤ m F0) → νSet-< m
Presheaf-νFace : ∀ m → (F0 : F0-< (2+ m)) → (Face : Face-≤ (1+ m) F0) 
               → ∀ p {δ} → [ p ≤ m ][ δ ]₂ → arity
               → fullframe (Presheaf-νSet-< (1+ m) F0 Face) .Dom
               → F0 .₁ .₂ .Dom

Presheaf-νSet-< 0 F0 Face = tt
Presheaf-νSet-< 1 F0 Face = tt , λ d → F0 .₁ .₂
Presheaf-νSet-< (2+ m) F0 Face =
 Presheaf-νSet-< (1+ m) (F0 .₁) (Face .₁) ,
 λ d → HΣ[ d' ∈ F0 .₁ .₂ ] HΠ[ r ∈ RestrInfo m ]
       H≡ (F0 .₁ .₁ .₂)
          (Presheaf-νFace m (F0 .₁) (Face .₁) _ (r .restr-p≤n) (r .restr-ε) d)
          (Face .₁ .₂ _ (r .restr-p≤n) (r .restr-ε) d')

Presheaf-νFace zero F0 Face p p≤m ε d = (νFace 0 p p≤m ε (Presheaf-νSet-< 1 F0 Face) d) .₂
Presheaf-νFace (1+ m) F0 Face p p≤m ε d = (νFace (1+ m) p p≤m ε (Presheaf-νSet-< (2+ m) F0 Face) d) .₂ .₁

Presheaf-νSet-> : ∀ m
              → (zipper : Presheaf-zipper m)
              → νSet-> m (Presheaf-νSet-< m (zipper .|F0-<| , zipper .|F0-≥| 0) (zipper .|Face-≤|))
Presheaf-νSet-> zero zipper .this d =  zipper .|F0-≥| 0
Presheaf-νSet-> zero zipper .next = Presheaf-νSet-> 1 (bump-zipper 0 zipper) 
Presheaf-νSet-> (1+ m) zipper .this d =
  HΣ[ d' ∈ zipper .|F0-≥| 0 ] HΠ[ r ∈ RestrInfo m ]
  H≡ (zipper .|F0-<| .₂)
     (Presheaf-νFace m (zipper .|F0-<| , zipper .|F0-≥| 0) (zipper .|Face-≤|) (r .restr-p) (r .restr-p≤n) (r .restr-ε) d)
     (zipper .|Face-≤| .₂ (r .restr-p) (r .restr-p≤n) (r .restr-ε) d')
Presheaf-νSet-> (1+ m) zipper .next = Presheaf-νSet-> (2+ m) (bump-zipper (1+ m) zipper)

f : Presheaf → νSet
f psh = Presheaf-νSet-> 0 (psh→zipper psh)

νSet-F0-< : ∀ m → νSet-< m → F0-< m 
νSet-F0-< zero D = tt
νSet-F0-< (1+ m) (D , E) = (νSet-F0-< m D) , (TotalSpace D E)

νSet-Face-≤ : ∀ m → (D : νSet-< (1+ m))
            → Face-≤ m (νSet-F0-< (1+ m) D)
νSet-Face-≤ zero D = tt
νSet-Face-≤ (1+ m) D = νSet-Face-≤ m (D .₁) ,  λ p p≤n ε d → νFace m p p≤n ε (D .₁) (d .₁)

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

f∘g-νSet₁ : (D : νSet-< 1) → (d : ⊤) → TotalSpace (D .₁) (D .₂) .Dom ≃ D .₂ d .Dom
f∘g-νSet₁ D d = ₂ , ((tt ,_) , λ _ → refl) , ((tt ,_) , λ _ → refl)

f∘g-νSet-< : ∀ m
           → (D : νSet-< (1+ m))
           → νSet-<-≃ (Presheaf-νSet-< m (νSet-F0-< (1+ m) D) (νSet-Face-≤ m D)) (D .₁)

f∘g-νSetₙ : ∀ m
          → (D : νSet-< (2+ m))
          → (d : fullframe (D .₁) .Dom)
          → (Σ[ d' ∈ TotalSpace (D .₁) (D .₂) .Dom ] ((r : RestrInfo m)
             → Presheaf-νFace m
                ( νSet-F0-< (2+ m) D)
                ( νSet-Face-≤ (1+ m) D)
                _ (r .restr-p≤n) (r .restr-ε)
                (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< (1+ m) D))) d)
             ≡ νFace m _ (r .restr-p≤n) (r .restr-ε) (D .₁) (d' .₁)))
          ≃ D .₂ d .Dom

f∘g-νFace-≡ : ∀ m
            → (D : νSet-< (2+ m))
            → (d : fullframe (D .₁) .Dom)
            → ∀ p {δ} (p≤m : [ p ≤ m ][ δ ]₂) ε
            → Presheaf-νFace m
                (νSet-F0-< (2+ m) D)
                (νSet-Face-≤ (1+ m) D)
                _ p≤m ε
                (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< (1+ m) D))) d)
            ≡ νFace m p p≤m ε (D .₁) d

f∘g-νSet-< 0 D = ≃[]
f∘g-νSet-< 1 D = ≃[] ≃∷ f∘g-νSet₁ (D .₁)
f∘g-νSet-< (2+ m) D = f∘g-νSet-< (1+ m) (D .₁) ≃∷ f∘g-νSetₙ m (D .₁)

f∘g-νSetₙ m (D , E) d = f' , (g' , g'∘f'∼id) , (g' , f'∘g'∼id)
 where

 f' : Σ[ dc ∈ TotalSpace D E .Dom ] ((r : RestrInfo m) →
      Presheaf-νFace m (νSet-F0-< (2+ m) (D , E)) (νSet-Face-≤ (1+ m) (D , E))
         (r .restr-p) (r .restr-p≤n) (r .restr-ε)
         (subst (λ - → fullframe - .Dom)
          (sym (νSet-<-≃→≡ (f∘g-νSet-< (1+ m) (D , E)))) d)
     ≡ νFace m (r .restr-p) (r .restr-p≤n) (r .restr-ε) D (dc .₁))
   → E d .Dom
 f' ((d' , c) , coh) = subst (λ - → E - .Dom)
   (νFace-≡ m D d' d λ p p≤n ε → sym (coh (info p _ ε p≤n)) ∙ f∘g-νFace-≡ m (D , E) d p p≤n ε) c

 g' : E d .Dom
    → Σ[ dc ∈ TotalSpace D E .Dom ] ((r : RestrInfo m) →
      Presheaf-νFace m (νSet-F0-< (2+ m) (D , E)) (νSet-Face-≤ (1+ m) (D , E))
         (r .restr-p) (r .restr-p≤n) (r .restr-ε)
         (subst (λ - → fullframe - .Dom)
          (sym (νSet-<-≃→≡ (f∘g-νSet-< (1+ m) (D , E)))) d)
     ≡ νFace m (r .restr-p) (r .restr-p≤n) (r .restr-ε) D (dc .₁))
 g' c = (_ , c) , λ r → f∘g-νFace-≡ m (D , E) d (r .restr-p) (r .restr-p≤n) (r .restr-ε)
 
 g'∘f'∼id : ∀ c → g' (f' c) ≡ c
 g'∘f'∼id ((d' , c) , coh) = Σ-≡→≡ (Σ-≡→≡
   ( sym (νFace-≡ m D d' d λ p p≤n ε → sym (coh (info p _ ε p≤n))
         ∙ f∘g-νFace-≡ m (D , E) d p p≤n ε)
   , subst-sym-l
       ((νFace-≡ m D d' d λ p p≤n ε → sym (coh (info p _ ε p≤n))
        ∙ f∘g-νFace-≡ m (D , E) d p p≤n ε)) c)
   , funExt λ r → TotalSpace (D .₁) (D .₂) .has-UIP _ _ _ (coh r)) 

 f'∘g'∼id : ∀ c → f' (g' c) ≡ c
 f'∘g'∼id c = cong (λ - → subst (λ - → E - .Dom) - c) (fullframe D .has-UIP _ _ _ refl) 

f∘g-νFace-≡ 0 (D , E) d p p≤m ε =
  νFace 0 p p≤m ε (tt , (λ d₁ → TotalSpace (D .₁) (D .₂)))
      (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (≃[] ≃∷ f∘g-νSet₁ D))) d) .₂
    ≡⟨ cong ₂ (νFace-νSet-<-≃ 0 _ _  (λ _ → TotalSpace (D .₁) (D .₂)) (D .₂) ≃[] (f∘g-νSet₁ D) d p p≤m ε) ⟩
  invEq (f∘g-νSet₁ D (νFace 0 p p≤m ε (tt , D .₂) d .₁)) (νFace 0 p p≤m ε (tt , D .₂) d .₂)
    ≡⟨⟩
  νFace zero p p≤m ε D d ∎ 
f∘g-νFace-≡ (1+ m) (D , E) d p p≤m ε =
   Presheaf-νFace (1+ m) (νSet-F0-< (3+ m) (D , E) ) (νSet-Face-≤ (2+ m) (D , E))
     _ p≤m ε (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (f∘g-νSet-< (2+ m) (D , E)))) d)
    ≡⟨ cong (λ - → - .₂ .₁) (νFace-νSet-<-≃ (1+ m)
           (Presheaf-νSet-< (1+ m) (νSet-F0-< (2+ m) D) (νSet-Face-≤ (1+ m) D))
           (D .₁)
           (λ d → HΣ[ d' ∈ TotalSpace (D .₁) (D .₂) ] HΠ[ r ∈ RestrInfo m ]
                   H≡ (TotalSpace (D .₁ .₁) (D .₁ .₂))
                      (Presheaf-νFace m _ _ _ (r .restr-p≤n) (r .restr-ε) d)
                      (νSet-Face-≤ (1+ m) D .₂ _ (r .restr-p≤n) (r .restr-ε) d'))
           (D .₂)
           (f∘g-νSet-< (1+ m) D)
           (f∘g-νSetₙ m D) d p p≤m ε) ⟩
   invEq (f∘g-νSetₙ m D (νFace (1+ m) p p≤m ε D d .₁))
     (νFace (1+ m) p p≤m ε D d .₂) .₁
    ≡⟨ refl ⟩
   νFace (1+ m) p p≤m ε D d ∎
f∘g-νSet-> : ∀ m
           → (D : νSet-< (1+ m)) (νSet : νSet-> (1+ m) D)
           → νSet->-≃ (f∘g-νSet-< (1+ m) (D , νSet .this))
              (Presheaf-νSet-> (1+ m) (νSet→zipper (1+ m) D νSet))
              νSet
f∘g-νSet-> m D νSet .this-≃ = f∘g-νSetₙ m (D , νSet .this)
f∘g-νSet-> m D νSet .next-≃ = f∘g-νSet-> (1+ m) (D , νSet .this) (νSet .next)

f∘g : ∀ νSet → νSet-≃ (f (g νSet)) νSet 
f∘g νSet .this-≃ = f∘g-νSet₁ (tt , νSet .this)
f∘g νSet .next-≃ = f∘g-νSet-> 0 (tt , νSet .this) (νSet .next)
