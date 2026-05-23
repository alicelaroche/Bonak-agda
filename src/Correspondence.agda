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

Presheaf-this : ∀ m → (D : Ctx m) (E : fullframe D .Dom → HSet)
              → (F0 : ∀ n {δ} → [ m ≤ n ][ δ ]₂ → HSet) 
              → (Face : ∀ n p {δ δ'} → (m≤n : [ m ≤ n ][ δ ]₂)
                      → [ p ≤ n ][ δ' ]₂
                      → arity
                      → F0 (1+ n) (↑₂ m≤n) .Dom
                      → F0 n m≤n .Dom)
              → (f : TotalSpace D E .Dom → F0 m (◆₂ m) .Dom)
              → fullframe (D ∷ E) .Dom → HSet
Presheaf-this m D E F0 Face f d =
 HΣ[ d' ∈ F0 (1+ m) (↑₂ ◆₂ m) ] HΠ[ r ∈ RestrInfo m ]
 H≡ (F0 m (◆₂ m))
  (f (νFace m _ (r .restr-p≤n) (r .restr-ε) D E d))
  (Face m _ (◆₂ m) (r .restr-p≤n) (r .restr-ε) d')

Presheaf-next : ∀ m → (D : Ctx m) (E : fullframe D .Dom → HSet)
              → (F0 : ∀ n {δ} → [ m ≤ n ][ δ ]₂ → HSet) 
              → (Face : ∀ n p {δ δ'} → (m≤n : [ m ≤ n ][ δ ]₂)
                      → [ p ≤ n ][ δ' ]₂
                      → arity
                      → F0 (1+ n) (↑₂ m≤n) .Dom
                      → F0 n m≤n .Dom)
              → (f : TotalSpace D E .Dom → F0 m (◆₂ m) .Dom)
              → νSet-> (1+ m) (D ∷ E)
Presheaf-next m D E F0 Face f .this = Presheaf-this m D E F0 Face f
Presheaf-next m D E F0 Face f .next =
  Presheaf-next (1+ m) (D ∷ E) (Presheaf-this m D E F0 Face f)
    (λ n m≤n → F0 n (↓₂ m≤n))
    (λ n p m≤n → Face n p (↓₂ m≤n))
    (λ dc → dc .₂ .₁)

f : Presheaf → νSet
f psh .this d = psh .F0 0
f psh .next =
  Presheaf-next 0 [] (λ _ → psh .F0 0)
   (λ n _ → psh .F0 n)
   (λ n p m≤n → psh .Face n p)
   (λ dc → dc .₂)

νSet-X : ∀ m n {δ} → [ m ≤ n ][ δ ]₂ → (D : Ctx m) → νSet-> m D
       → HSet
νSet-X m n {zero} (ineq₂ Hmn) D νSet with recover-nat-eq m n Hmn
... | refl = TotalSpace D (νSet .this)
νSet-X m n {1+ δ} m≤n D νSet =
  νSet-X (1+ m) n (←₂ m≤n) (D ∷ νSet .this) (νSet .next)

νSet-Face : ∀ m n p {δ δ'}
          → (m≤n : [ m ≤ n ][ δ ]₂)
          → (D : Ctx m) (νSet : νSet-> m D)
          → [ p ≤ n ][ δ' ]₂
          → arity
          → νSet-X m (1+ n) (↑₂ m≤n) D νSet .Dom
          → νSet-X m n m≤n D νSet .Dom
νSet-Face m n p {zero} (ineq₂ Hmn) D νSet p≤n ε d with recover-nat-eq m n Hmn
... | refl = νFace n p p≤n ε D (νSet .this) (d .₁)
νSet-Face m n p {1+ δ} m≤n D νSet p≤n ε d =
  νSet-Face (1+ m) n p (←₂ m≤n) _ (νSet .next) p≤n ε d

νSet-Face-coh : ∀ m n p q {δ δ'}
              → (m≤n : [ m ≤ n ][ δ ]₂)
              → (D : Ctx m) (νSet : νSet-> m D)
              → (p≤q≤n : [ p ≤ q ≤ n ][ δ' ]₃) 
              → (ε ω : arity)
              → (d : νSet-X m (2+ n) (↑₂ ↑₂ m≤n) D νSet .Dom)
              → νSet-Face m n q m≤n D νSet (drop₃-1 p≤q≤n) ε 
                 (νSet-Face m (1+ n) p (↑₂ m≤n) D νSet (↑₂ drop₃-2 p≤q≤n) ω d)
              ≡ νSet-Face m n p m≤n D νSet (drop₃-2 p≤q≤n) ω
                 (νSet-Face m (1+ n) (1+ q) (↑₂ m≤n) D νSet (⇑₂ drop₃-1 p≤q≤n) ε d)
νSet-Face-coh m n p q {zero} (ineq₂ Hmn) D νSet p≤q≤n ε ω d with recover-nat-eq m n Hmn
... | refl = νFace-coh n p q p≤q≤n ε ω _ _ _ (d .₁)
νSet-Face-coh m n p q {1+ δ} m≤n D νSet p≤q≤n ε ω d =
  νSet-Face-coh (1+ m) n p q (←₂ m≤n) _ (νSet .next) p≤q≤n ε ω d

g : νSet → Presheaf
g νSet .F0 n = νSet-X 0 n (0≤n n) [] νSet
g νSet .Face n p = νSet-Face 0 n p (0≤n n) [] νSet
g νSet .Face-coh n p q = νSet-Face-coh 0 n p q (0≤n n) [] νSet

f∘g-this : ∀ m
         → (D : Ctx m) (νSet : νSet-> m D)
         → (D' : Ctx m) (E' : fullframe D' .Dom → HSet)
         → (D-≃ : Ctx-≃ (D' ∷ E') (D ∷ νSet .this))
         → (f : TotalSpace D' E' .Dom → νSet-X m m (◆₂ m) D νSet .Dom)
         → (f-≡ : ∀ p {δ} (p≤n : [ p ≤ m ][ δ ]₂) ε d
                → f (νFace m p p≤n ε D' E' d)
                ≡ νFace m p p≤n ε D (νSet .this) (subst (λ - → fullframe - .Dom) (Ctx-≃→≡ D-≃) d))
         → (d : fullframe (D ∷ νSet .this) .Dom)
         → Presheaf-this m D' E'
             (λ n m≤n → νSet-X m n m≤n _ νSet)
             (λ n p m≤n p≤n → νSet-Face m n p m≤n _ νSet p≤n) f
             (subst (λ - → fullframe - .Dom) (sym (Ctx-≃→≡ D-≃)) d) .Dom
         ≃ νSet .next .this d .Dom
f∘g-this m D νSet D' E' D-≃ f f-≡ d = f' , {!!}
 where
 f' : Presheaf-this m D' E'
        (λ n m≤n → νSet-X m n m≤n _ νSet)
        (λ n p m≤n p≤n → νSet-Face m n p m≤n _ νSet p≤n) f
        (subst (λ - → fullframe - .Dom) (sym (Ctx-≃→≡ D-≃)) d) .Dom
    → νSet .next .this d .Dom
 f' ((d' , c) , coh) = subst (λ - → νSet .next .this - .Dom)
  ((νFace-≡ m _ _ _ _ λ p p≤n ε → sym (coh (info p _ ε p≤n)) ∙ f-≡ p p≤n ε _) ∙ subst-sym-r (Ctx-≃→≡ D-≃) d) c

f∘g-next : ∀ m
         → (D : Ctx m) (νSet : νSet-> m D)
         → (D' : Ctx m) (E' : fullframe D' .Dom → HSet)
         → (D-≃ : Ctx-≃ (D' ∷ E') (D ∷ νSet .this))
         → (f : TotalSpace D' E' .Dom → νSet-X m m (◆₂ m) D νSet .Dom)
         → (f-≡ : ∀ p {δ} (p≤n : [ p ≤ m ][ δ ]₂) ε d
                → f (νFace m p p≤n ε D' E' d)
                ≡ νFace m p p≤n ε D (νSet .this) (subst (λ - → fullframe - .Dom) (Ctx-≃→≡ D-≃) d))
         → νSet->-≃ D-≃
             (Presheaf-next m D' E'
               (λ n m≤n → νSet-X m n m≤n _ νSet)
               (λ n p m≤n p≤n → νSet-Face m n p m≤n _ νSet p≤n) f)
               (νSet .next)
f∘g-next m D νSet D' E' D-≃ f f-≡ .this-≃ d =
  f∘g-this m D νSet D' E' D-≃ f f-≡ d 
f∘g-next m D νSet D' E' D-≃ f f-≡ .next-≃ =
 f∘g-next (1+ m) (D ∷ νSet .this) (νSet .next) (D' ∷ E') E''
   (D-≃ ∷≃ f∘g-this m D νSet D' E' D-≃ f f-≡)
   (λ dc → dc .₂ .₁)
   f-≡'
 where
 E'' : fullframe (D' ∷ E') .Dom → HSet
 E'' = Presheaf-this m D' E'
         (λ n m≤n → νSet-X m n m≤n _ νSet)
         (λ n p m≤n p≤n → νSet-Face m n p m≤n _ νSet p≤n)
         f

 f-≡' : ∀ p {δ} (p≤n : [ p ≤ 1+ m ][ δ ]₂) ε d
      → νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂ .₁
      ≡ νFace (1+ m) p p≤n ε (D ∷ νSet .this) (νSet .next .this)
         (subst (λ - → fullframe - .Dom)
         (Ctx-≃→≡ (D-≃ ∷≃ f∘g-this m D νSet D' E' D-≃ f f-≡)) d)
 f-≡' p p≤n ε d =
   νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂ .₁
     ≡⟨⟩
   νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂ .₁ .₁ ,
   νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂ .₁ .₂
     ≡⟨ Σ-≡→≡ (νFace-≡ m D (νSet .this) _ _
         (λ q q≤n ω → sym (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂ .₂ (info q _ ω q≤n))
                    ∙ f-≡ q q≤n ω (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₁))
         , refl) ⟩
   subst (λ - → fullframe - .Dom) (Ctx-≃→≡ D-≃)
     (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₁) ,
   subst (λ - → νSet .next .this - .Dom)
       (νFace-≡ m D (νSet .this) _ _
         (λ q q≤n ω →
            sym (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂ .₂ (info q _ ω q≤n))
         ∙ f-≡ q q≤n ω (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₁)))
      (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂ .₁ .₂)
     ≡⟨ Σ-≡→≡ (refl , {!!}) ⟩
   subst (λ - → fullframe - .Dom) (Ctx-≃→≡ D-≃)
     (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₁) ,
   subst (λ - → νSet .next .this - .Dom)
     (νFace-≡ m D (νSet .this) _ _
       (λ q q≤n ω →
           sym ((subst (λ - → E'' - .Dom) (sym (subst-sym-l (Ctx-≃→≡ D-≃) _))
            (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂)) .₂ (info q _ ω q≤n))
       ∙ f-≡ q q≤n ω _)
     ∙ subst-sym-r (Ctx-≃→≡ D-≃) _)
     (subst (λ - → E'' - .Dom) (sym (subst-sym-l (Ctx-≃→≡ D-≃) _))
       (νFace (1+ m) p p≤n ε (D' ∷ E') E'' d .₂) .₁ .₂)
     ≡⟨ sym (Ctx-≃-Face-subst D-≃ (f∘g-this m D νSet D' E' D-≃ f f-≡) p p≤n ε d)  ⟩
   νFace (1+ m) p p≤n ε (D ∷ νSet .this) (νSet .next .this)
     (subst (λ - → fullframe - .Dom)
     (Ctx-≃→≡ (D-≃ ∷≃ f∘g-this m D νSet D' E' D-≃ f f-≡)) d) ∎ 

f∘g-base : ∀ νSet d → f (g νSet) .this d .Dom ≃ νSet .this d .Dom
f∘g-base νSet d = (λ t → {!!}) , {!!} , {!!}
--₂ , ((tt ,_) , (λ _ → refl)) , ((tt ,_) , λ _ → refl)

f∘g : ∀ νSet → νSet-≃ (f (g νSet)) νSet 
f∘g νSet .this-≃ = f∘g-base νSet
f∘g νSet .next-≃ = {!f∘g-next 0 [] νSet [] ? ([]≃ ∷≃ f∘g-base νSet) (λ c → c .₂) ?!}
