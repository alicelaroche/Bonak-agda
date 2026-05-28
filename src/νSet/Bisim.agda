open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module νSet.Bisim
    (fe-axiom : FunExt-Axiom)
    (ua-axiom : Univalence-Axiom)
    (arity : Type)
 where

open import Equiv
open import Inequalities
open import HSet

open import νSet.Base fe-axiom arity
open import νSet.Face fe-axiom arity

open FE fe-axiom
open UA ua-axiom
open HSet-FE fe-axiom

opaque
  νSet-<-≃ : ∀ {n} → (D D' : νSet-< n) → Type₁
  νSet-<-≃→≡ : ∀ {n} → {D D' : νSet-< n} → νSet-<-≃ D D' → D ≡ D'
  
  νSet-<-≃ {zero} D D' = ⊤
  νSet-<-≃ {1+ n} (D , E) (D' , E') =
    Σ[ D≡D' ∈ νSet-<-≃ D D' ]
    (∀ d → E (subst (λ - → frame n n (◆₂ n) - .Dom) (sym (νSet-<-≃→≡ D≡D')) d) .Dom ≃ E' d .Dom)
  
  νSet-<-≃→≡ {zero} D≃D' = refl
  νSet-<-≃→≡ {1+ n} {D , E} {D' , E'} (D≡D' , E≡E') =
    Σ-≡→≡ ((νSet-<-≃→≡ D≡D') , subst-fun-l (νSet-<-≃→≡ D≡D') (λ - → E -) ∙ funExt λ d → HSet-≡ _ (E' d) (ua (E≡E' d)))

  ≃[] : νSet-<-≃ tt tt
  ≃[] = tt

  _≃∷_ : ∀ {n}
      → {D D' : νSet-< n}
      → {E : fullframe D .Dom → HSet} {E' : fullframe D' .Dom → HSet}
      → (D≃D' : νSet-<-≃ D D')
      → (E≃E' : ∀ d → E (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) d) .Dom
                    ≃ E' d .Dom)
      → νSet-<-≃ (D , E) (D' , E')
  _≃∷_ D≃D' E≃E' = D≃D' , E≃E'

  νFace-νSet-<-≃ : ∀ n
      → (D D' : νSet-< n)
      → (E : fullframe D .Dom → HSet) (E' : fullframe D' .Dom → HSet)
      → (D≃D' : νSet-<-≃ D D')
      → (E≃E' : ∀ d → E (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) d) .Dom
                    ≃ E' d .Dom)
      → (d : fullframe (D' , E') .Dom)
      → ∀ p {δ} (p≤n : [ p ≤ n ][ δ ]₂) (ε : arity)
      → νFace n p p≤n ε (D , E) (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ (D≃D' ≃∷ E≃E'))) d)
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
  
record νSet->-≃ {n} {D D' : νSet-< n}
  (D≃D' : νSet-<-≃ D D')
  (νSet : νSet-> n D) (νSet' : νSet-> n D') : Type₁
  where
  coinductive
  field
   this-≃ : ∀ d → νSet .this (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) d) .Dom
                ≃ νSet' .this d .Dom
   next-≃ : νSet->-≃ (D≃D' ≃∷ this-≃) (νSet .next) (νSet' .next)

open νSet->-≃ public

νSet-≃ : (νSet νSet' : νSet) → Type₁
νSet-≃ νSet νSet' = νSet->-≃ ≃[] νSet νSet' 
