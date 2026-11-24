{-# OPTIONS --termination-depth=3 #-}

open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module Correspondence.Inverses
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

open import Correspondence.PresheafToνSet fe-axiom ua-axiom arity
open import Correspondence.νSetToPresheaf fe-axiom ua-axiom arity

open FE fe-axiom
open UA ua-axiom

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

opaque
  νFace-νSet-<-≃ : ∀ n
      → (D D' : νSet-< n)
      → (E : fullframe D .Dom → HSet) (E' : fullframe D' .Dom → HSet)
      → (D≃D' : νSet-<-≃ D D')
      → (E≃E' : ∀ d → E (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) d) .Dom
                    ≃ E' d .Dom)
      → (d : fullframe (D' , E') .Dom)
      → ∀ p {δ} (p≤n : [ p ≤ n ][ δ ]₂) (ε : arity)
      → νFace n p p≤n ε (D , E) (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (D≃D' , E≃E'))) d)
      ≡ ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) (νFace n p p≤n ε (D' , E') d .₁)
        , invEq (E≃E' (νFace n p p≤n ε (D' , E') d .₁)) (νFace n p p≤n ε (D' , E') d .₂))
  νFace-νSet-<-≃ n D D' E E' D≃D' E≃E' d p p≤n ε =
   νFace n p p≤n ε (D , E) (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (D≃D' , E≃E'))) d)
    ≡⟨ subst-application (λ - → fullframe - .Dom) (νFace n p p≤n ε) (sym (νSet-<-≃→≡ (D≃D' , E≃E'))) ⟩⁻¹
   subst (λ - → TotalSpace (- .₁) (- .₂) .Dom) {a = D' , E'} {a' = D , E}
     (sym (νSet-<-≃→≡ (D≃D' , E≃E'))) (νFace n p p≤n ε (D' , E') d)
    ≡⟨ J {A = νSet-< n} {x = D}
        (λ D' D≡D'
        → (∀ E' (E≃E' : (d : fullframe D' .Dom)
                      → E (subst (λ - → fullframe - .Dom) (sym D≡D') d) .Dom
                      ≃ E' d .Dom)  d
        → subst (λ - → TotalSpace (- .₁) (- .₂) .Dom) {a = D' , E'} {a' = D , E}
                 (sym (Σ-≡→≡ (D≡D' , subst-fun-l D≡D' (λ - → E -) ∙ funExt λ d → HSet-≡ _ (E' d) (ua (E≃E' d)))))
                (νFace n p p≤n ε (D' , E') d)
        ≡ ( subst (λ - → fullframe - .Dom) (sym D≡D') (νFace n p p≤n ε (D' , E') d .₁)
          , subst (λ - → - (νFace n p p≤n ε (D' , E') d .₁) .Dom)
              {a = E'} {a' = E ∘ subst (λ - → fullframe - .Dom) (sym D≡D')}
              (sym (funExt λ d → HSet-≡ _ (E' d) (ua (E≃E' d))))
              (νFace n p p≤n ε (D' , E') d .₂))))
       (λ E' E≃E' d →
      J {A = fullframe D .Dom → HSet} {x = E}
       (λ E' E≡E'
       → ∀ d
       → subst (λ - → TotalSpace (- .₁) (- .₂) .Dom) {a = D , E'} {a' = D , E}
           (sym (Σ-≡→≡ (refl , E≡E'))) (νFace n p p≤n ε (D , E') d)
       ≡ ( νFace n p p≤n ε (D , E') d .₁
         , subst (λ - → - (νFace n p p≤n ε (D , E') d .₁) .Dom) (sym E≡E') (νFace n p p≤n ε (D , E') d .₂)))
       (λ d → refl) (funExt λ d → HSet-≡ _ (E' d) (ua (E≃E' d))) d)
      (νSet-<-≃→≡ D≃D') E' E≃E' d ⟩
   ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) (νFace n p p≤n ε (D' , E') d .₁)
   , subst (λ - → - (νFace n p p≤n ε (D' , E') d .₁) .Dom)
       (sym (funExt λ d → HSet-≡ _ (E' d) (ua (E≃E' d)))) (νFace n p p≤n ε (D' , E') d .₂))
    ≡⟨ Σ-≡→≡ (refl , helper d) ⟩
   ( subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) (νFace n p p≤n ε (D' , E') d .₁)
   , E≃E' (νFace n p p≤n ε (D' , E') d .₁) .₂ .₁ .₁ (νFace n p p≤n ε (D' , E') d .₂)) ∎
   where
   helper : ∀ d
          → subst (λ - → - (νFace n p p≤n ε (D' , E') d .₁) .Dom)
              {a' = E ∘ (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D'))) }
              (sym (funExt λ d → HSet-≡ _ (E' d) (ua (E≃E' d)))) (νFace n p p≤n ε (D' , E') d .₂)
          ≡ E≃E' (νFace n p p≤n ε (D' , E') d .₁) .₂ .₁ .₁ (νFace n p p≤n ε (D' , E') d .₂)
   helper d =
    subst (λ - → - (νFace n p p≤n ε (D' , E') d .₁) .Dom)
      (sym (funExt λ d → HSet-≡ _ (E' d) (ua (E≃E' d)))) (νFace n p p≤n ε (D' , E') d .₂)
     ≡⟨ cong (λ - → subst (λ - → - (νFace n p p≤n ε (D' , E') d .₁) .Dom) - _)
         (funExt-sym (λ d → HSet-≡ _ (E' d) (ua (E≃E' d)))) ⟩
    subst (λ - → - (νFace n p p≤n ε (D' , E') d .₁) .Dom)
      (funExt λ d → sym (HSet-≡ _ (E' d) (ua (E≃E' d)))) (νFace n p p≤n ε (D' , E') d .₂)
     ≡⟨ funExt-subst (λ d → sym (HSet-≡ _ (E' d) (ua (E≃E' d))))
         (νFace n p p≤n ε (D' , E') d .₁) (νFace n p p≤n ε (D' , E') d .₂) ⟩
    subst (λ - → - .Dom)
      (sym (HSet-≡ _ (E' (νFace n p p≤n ε (D' , E') d .₁)) (ua (E≃E' (νFace n p p≤n ε (D' , E') d .₁)))))
      (νFace n p p≤n ε (D' , E') d .₂)
     ≡⟨ cong (λ - → subst (λ - → - .Dom) - (νFace n p p≤n ε (D' , E') d .₂))
             (HSet-≡-sym _ _ (ua (E≃E' (νFace n p p≤n ε (D' , E') d .₁)))) ⟩
    subst (λ - → - .Dom)
      (HSet-≡ (E' (νFace n p p≤n ε (D' , E') d .₁)) _ (sym (ua (E≃E' (νFace n p p≤n ε (D' , E') d .₁)))))
      (νFace n p p≤n ε (D' , E') d .₂)
     ≡⟨ HSet-≡-subst _ _  (sym (ua (E≃E' (νFace n p p≤n ε (D' , E') d .₁)))) {c = (νFace n p p≤n ε (D' , E') d .₂)} ⟩
    transport (sym (ua (E≃E' (νFace n p p≤n ε (D' , E') d .₁))))
     (νFace n p p≤n ε (D' , E') d .₂)
     ≡⟨ happly (ua-β' (E≃E' (νFace n p p≤n ε (D' , E') d .₁))) _  ⟩
    invEq (E≃E' (νFace n p p≤n ε (D' , E') d .₁)) (νFace n p p≤n ε (D' , E') d .₂) ∎

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
f∘g-νSet-< (1+ m) D = f∘g-νSet-< m (D .₁) , f∘g-νSetₙ m (D .₁)

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
    ≡⟨ νFace-νSet-<-≃ m _ _ _ _ (f∘g-νSet-< m (D .₁)) (f∘g-νSetₙ m (D .₁)) d p p≤n ε ⟩
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
  Presheaf-frame m (νSet-psh-< (D .₁)) m (◆₂ m) (νFace m p p≤n ε (D .₁ .₁) d) ,
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
