open import Prelude

module Correspondence
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
open HΠ fe fe-≡

open import Category arity
open import νSet fe fe-≡ arity

module _ (psh : Presheaf') where
  Presheaf-this : ∀ n → (D : νSet-< (1+ n))
                → (f : ∀ d → painting n n (◆₂ n) (D .₁) (D .₂) d .Dom
                           → psh .F0 n .Dom)
                → frame (1+ n) (1+ n) (◆₂ (1+ n)) D .Dom
                → HSet
  Presheaf-this n D f d =
    HΣ[ x ∈ psh .F0 (1+ n) ] HΠ[ r ∈ RestrInfo n ] 
      H≡ (psh .F0 n)
         (f _ (νFace n _ (r .restr-p≤n) (r .restr-ε) D d .₂))
         (psh .Face n _ (r .restr-p≤n) (r .restr-ε) x)

  Presheaf-next : ∀ n
                 → (D : νSet-< (1+ n))
                 → (f : ∀ d → painting n n (◆₂ n) (D .₁) (D .₂) d .Dom
                            → psh .F0 n .Dom)
                 → νSet-> (1+ n) D
  Presheaf-next n D f .this = Presheaf-this n D f
  Presheaf-next n D f .next =
    Presheaf-next (1+ n) (D , Presheaf-this n D f) (λ d c → c .₁)
  
  f : νSet
  f .this d = psh .F0 0
  f .next = Presheaf-next 0 (tt , λ _ → psh .F0 0) (λ d c → c)

module _ (νSet : νSet) where 
  X-aux : ∀ (k n : ℕ)
        → (D : νSet-< n) → νSet-> n D
        → HSet
  X-aux zero   n D νSet = HΣ[ d ∈ frame n n (◆₂ n) D ] painting n n (◆₂ n) D (νSet .this) d
  X-aux (1+ k) n D νSet = X-aux k (1+ n) (D , (νSet .this)) (νSet .next)

  Face-aux : ∀ (k n p : ℕ) → [ p ≤ k + n ]₂
           → arity
           → (D : νSet-< n) (νSet : νSet-> n D)
           → X-aux (1+ k) n D νSet .Dom
           → X-aux k n D νSet .Dom
  Face-aux zero n p p≤k+n ε D νSet (d , c) =
    νFace n p p≤k+n ε (D , νSet .this) d
  Face-aux (1+ k) n p p≤k+n ε D νSet X =
    Face-aux k (1+ n) p p≤k+n ε _ (νSet .next) X

  Face-aux-coh : ∀ k n p q → (p≤q≤n : [ p ≤ q ≤ k + n ]₃) 
               → (ε ω : arity)
               → (D : νSet-< n) (νSet : νSet-> n D)
               → (X : X-aux (2+ k) n D νSet .Dom)
               → Face-aux k n q (drop₃-1 p≤q≤n) ε D νSet
                  (Face-aux (1+ k) n p (↑₂ drop₃-2 p≤q≤n) ω D νSet X )
               ≡ Face-aux k n p (drop₃-2 p≤q≤n) ω D νSet
                  (Face-aux (1+ k) n (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D νSet X )
  Face-aux-coh zero n p q p≤q≤n ε ω D νSet (d , c) =
    νFace-coh n p q p≤q≤n ε ω _ d
  Face-aux-coh (1+ k) n p q p≤q≤n ε ω D νSet X =
   Face-aux-coh k (1+ n) p q p≤q≤n ε ω _ (νSet .next) X

  νSet-X : ℕ → HSet
  νSet-X n = X-aux n 0 tt νSet

  νSet-Face : ∀ n p → [ p ≤ n ]₂ → arity
            → νSet-X (1+ n) .Dom → νSet-X n .Dom
  νSet-Face n p p≤n ε X = Face-aux n 0 p p≤n ε tt νSet X

  νSet-Face-coh : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃) 
                → (ε ω : arity)
                → (X : νSet-X (2+ n) .Dom)
                → νSet-Face n q (drop₃-1 p≤q≤n) ε
                    (νSet-Face (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω X) 
                ≡ νSet-Face n p (drop₃-2 p≤q≤n) ω
                    (νSet-Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε X)
  νSet-Face-coh n p q p≤q≤n ε ω X = Face-aux-coh n 0 p q p≤q≤n ε ω tt νSet X

  g : Presheaf'
  g .F0 = νSet-X
  g .Face = νSet-Face
  g .Face-coh = νSet-Face-coh
