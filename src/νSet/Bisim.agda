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
  unfolding Ctx
  
  Ctx-≃ : ∀ {n} → (D D' : Ctx n) → Type₁
  Ctx-≃→≡ : ∀ {n} → {D D' : Ctx n} → Ctx-≃ D D' → D ≡ D'

  Ctx-≃ {zero} D D' = ⊤
  Ctx-≃ {1+ n} (D , E) (D' , E') =
    Σ[ D≡D' ∈ Ctx-≃ D D' ]
    (∀ d → E (subst (λ - → frame n n (◆₂ n) - .Dom) (sym (Ctx-≃→≡ D≡D')) d) .Dom ≃ E' d .Dom)

  Ctx-≃→≡ {zero} D≃D' = refl
  Ctx-≃→≡ {1+ n} {D , E} {D' , E'} (D≡D' , E≡E') =
    Σ-≡→≡ ((Ctx-≃→≡ D≡D') , funExt λ d → HSet-≡ _ _ (I d))
    where
    I : ∀ d → subst (νSet-= n) (Ctx-≃→≡ D≡D') E d .Dom ≡ E' d .Dom
    I d =
      subst (νSet-= n) (Ctx-≃→≡ D≡D') E d .Dom
        ≡⟨ cong (λ - → - d .Dom) (subst-∘ {C = λ - → - → HSet} (Ctx-≃→≡ D≡D') _) ⟩
      subst (λ - → - → HSet) (cong (λ - → frame n n (◆₂ n) - .Dom) (Ctx-≃→≡ D≡D')) E d .Dom
        ≡⟨ cong (λ - → - d .Dom) (subst-fun-l (cong (λ - → frame n n (◆₂ n) - .Dom) (Ctx-≃→≡ D≡D')) E) ⟩
      E (transport (sym (cong (λ - → frame n n (◆₂ n) - .Dom) (Ctx-≃→≡ D≡D'))) d) .Dom 
        ≡⟨ cong (λ - → E (subst (λ - → -) - d) .Dom  ) (cong-sym _ _) ⟩
      E (transport (cong (λ - → frame n n (◆₂ n) - .Dom) (sym (Ctx-≃→≡ D≡D'))) d) .Dom
        ≡⟨ cong (λ - → E - .Dom) (subst-∘ (sym (Ctx-≃→≡ D≡D')) _) ⟩⁻¹
      E (subst (λ - → frame n n (◆₂ n) - .Dom) (sym (Ctx-≃→≡ D≡D')) d) .Dom 
        ≡⟨ ua (E≡E' d) ⟩
      E' d .Dom ∎

  []≃ : Ctx-≃ [] []
  []≃ = tt 

  _∷≃_ : ∀ {n} {D D' : Ctx n}
       → {E : fullframe D .Dom → HSet} {E' : fullframe D' .Dom → HSet}
       → (D≃D' : Ctx-≃ D D')
       → (∀ d → E (subst (λ - → fullframe - .Dom) (sym (Ctx-≃→≡ D≃D')) d) .Dom
              ≃ E' d .Dom)
       → Ctx-≃ (D ∷ E) (D' ∷ E')
  _∷≃_ D≃D' E≃E' = D≃D' , E≃E'

  postulate
   Ctx-≃-Face-subst : ∀ {n} {D D' : Ctx n}
                   → {E : fullframe D .Dom → HSet} {E' : fullframe D' .Dom → HSet}
                   → (D≃D' : Ctx-≃ D D')
                   → (E≃E' : ∀ d → E (subst (λ - → fullframe - .Dom) (sym (Ctx-≃→≡ D≃D')) d) .Dom
                                 ≃ E' d .Dom)
                   → ∀ p {δ} (p≤n : [ p ≤ n ][ δ ]₂) ε
                   → (d : fullframe (D ∷ E) .Dom)
                   → νFace n p p≤n ε D' E' (subst (λ - → fullframe - .Dom) (Ctx-≃→≡ (D≃D' ∷≃ E≃E')) d)
                   ≡ ( subst (λ - → fullframe - .Dom) (Ctx-≃→≡ D≃D') (νFace n p p≤n ε D E d .₁) 
                     , equivFun (E≃E' _)
                        (subst (λ - → E - .Dom) (sym (subst-sym-l (Ctx-≃→≡ D≃D') _)) (νFace n p p≤n ε D E d .₂)))

record νSet->-≃ {n} {D D' : Ctx n}
  (D≃D' : Ctx-≃ D D')
  (νSet : νSet-> n D) (νSet' : νSet-> n D') : Type₁
  where
  coinductive
  field
   this-≃ : ∀ d → νSet .this (subst (λ - → fullframe - .Dom) (sym (Ctx-≃→≡ D≃D')) d) .Dom
                ≃ νSet' .this d .Dom
   next-≃ : νSet->-≃ (D≃D' ∷≃ this-≃) (νSet .next) (νSet' .next)
open νSet->-≃ public

νSet-≃ : (νSet νSet' : νSet) → Type₁
νSet-≃ νSet νSet' = νSet->-≃ []≃ νSet νSet' 
