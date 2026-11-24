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

open FE fe-axiom
open UA ua-axiom
open HSet-FE fe-axiom

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

record νSet->-≃ {n} {D D' : νSet-< n}
  (D≃D' : νSet-<-≃ D D')
  (νSet : νSet-> n D) (νSet' : νSet-> n D') : Type₁
  where
  coinductive
  field
   this-≃ : ∀ d → νSet .this (subst (λ - → fullframe - .Dom) (sym (νSet-<-≃→≡ D≃D')) d) .Dom
                ≃ νSet' .this d .Dom
   next-≃ : νSet->-≃ (D≃D' , this-≃) (νSet .next) (νSet' .next)

open νSet->-≃ public

νSet-≃ : (νSet νSet' : νSet) → Type₁
νSet-≃ νSet νSet' = νSet->-≃ ≃[] νSet νSet' 
