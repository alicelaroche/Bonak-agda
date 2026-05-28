module Prelude where

open import Agda.Primitive renaming (Set to Type; Setω to Typeω) public

id : ∀ {ℓ} {A : Type ℓ} → A → A
id x = x

data ⊥ : Type where

record ⊤ {ℓ} : Type ℓ where
  instance constructor tt
{-# BUILTIN UNIT ⊤ #-}

infix 4 _≡_
data _≡_ {ℓ} {A : Type ℓ} (x : A) : A → Type ℓ where
  refl : x ≡ x

{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REWRITE _≡_  #-}

sym : ∀ {ℓ} {A : Type ℓ} {a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl q = q

trans' : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' p refl = p

infixr 30 _∙_ _∙'_
_∙_ = trans
_∙'_ = trans'

infixr 9 _∘_
_∘_ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : (a : A) → B a → Type ℓ''}
    → (g : {a : A} → (b : B a) → C a b)
    → (f : (a : A) → B a)
    → (a : A)→ C a (f a)
g ∘ f = λ x → g (f x)
{-# INLINE _∘_ #-}

cong : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a a' : A} → (f : A → B)
     → a ≡ a' → f a ≡ f a'
cong f refl = refl

happly : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A -> Type ℓ'} {f g : (a : A) → B a}
         → f ≡ g → (a : A) → f a ≡ g a
happly refl a = refl

happly-impl : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A -> Type ℓ'} {f g : {a : A} → B a}
            → (λ {x} → f {x}) ≡ (λ {x} → g {x})  → (a : A) → f {a} ≡ g {a}
happly-impl refl a = refl

subst : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {a a' : A} → a ≡ a' → B a → B a'
subst B refl b = b

dsubst : ∀ {ℓ ℓ' ℓ''} {X : Type ℓ}
       → (A : X -> Type ℓ') (B : (x : X) → A x → Type ℓ'')
       → {x y : X} {a : A x}
       → (p : x ≡ y)
       → B x a
       → B y (subst A p a)
dsubst A B refl b = b

transport : ∀ {ℓ} {A B : Type ℓ} → A ≡ B → A → B
transport = subst (λ x → x) 

dcong : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (f : (x : A) → B x) {x y}
      → (p : x ≡ y) → subst B p (f x) ≡ f y
dcong f refl = refl

cong₂ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : Type ℓ''} {a a' : A} {b : B a}
      → (f : (a : A) → B a → C)
      → (p : a ≡ a') → f a b ≡ f a' (subst B p b)
cong₂ f refl = refl

trans-assoc : ∀ {ℓ} {A : Type ℓ} {x y z w : A}
            → (p : x ≡ y) (q : y ≡ z) (r : z ≡ w)
            → trans (trans p q) r ≡ trans p (trans q  r)
trans-assoc refl q r = refl

trans-identity-l : ∀ {ℓ} {A : Type ℓ} {a a' : A} (p : a ≡ a')
                 → trans refl p ≡ p
trans-identity-l H = refl

trans-identity-r : ∀ {ℓ} {A : Type ℓ} {a a' : A} (p : a ≡ a')
                 → trans p refl ≡ p
trans-identity-r refl = refl

trans-sym-l : ∀ {ℓ} {A : Type ℓ} {a a' : A} (p : a ≡ a')
            → (sym p) ∙ p ≡ refl
trans-sym-l refl = refl

trans-sym-r : ∀ {ℓ} {A : Type ℓ} {a a' : A} (p : a ≡ a')
            → p ∙ (sym p) ≡ refl
trans-sym-r refl = refl

subst-dup : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → A → Type ℓ') {a a' : A}
            → (p : a ≡ a') (b : B a a)
            → subst (λ - → B - -) p b
            ≡ subst (λ - → B - a') p (subst (B a) p b)
subst-dup B refl b = refl

subst-const : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a a' : A}
            → (p : a ≡ a') (b : B)
            → subst (λ - → B) p b ≡ b
subst-const refl b = refl

subst-sym-l' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a a' : A}
            → (p : a ≡ a')
            → subst B (sym p) ∘ subst B p ≡ id
subst-sym-l' refl = refl

subst-sym-r' : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a a' : A}
            → (p : a ≡ a') 
            → subst B p ∘ subst B (sym p) ≡ id
subst-sym-r' refl = refl

subst-sym-l : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a a' : A}
            → (p : a ≡ a') (b : B a)
            → subst B (sym p) (subst B p b) ≡ b
subst-sym-l p = happly (subst-sym-l' p)

subst-sym-r : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a a' : A}
            → (p : a ≡ a') (b : B a')
            → subst B p (subst B (sym p) b) ≡ b
subst-sym-r p = happly (subst-sym-r' p)

subst-paths-l : ∀ {ℓ} {A : Type ℓ} {x y y' : A} (p : x ≡ y) (q : y ≡ y')
              → subst (λ y → x ≡ y) q p ≡ p ∙ q
subst-paths-l p refl = sym (trans-identity-r p)

subst-paths-r : ∀ {ℓ} {A : Type ℓ} {x x' y : A} (p : x ≡ x') (q : x ≡ y)
              → subst (λ x →  x ≡ y) p q ≡ sym p ∙ q
subst-paths-r refl p = refl

subst-∘ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {x y : A} {C : B → Type ℓ''}
        → {f : A → B}
        → (x≡y : x ≡ y) (c : C (f x))
        → subst (λ - → C (f -)) x≡y c ≡ subst C (cong f x≡y) c
subst-∘ refl c = refl

subst-∘' : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {x : A} {C : B x → Type ℓ''}
          → {f g : (a : A) → B a}
          → (f≡g : f ≡ g) (c : C (f x))
          → subst (λ - → C (- x)) f≡g c ≡ subst C (happly f≡g x) c
subst-∘' refl c = refl

subst-fun-r : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : A → Type ℓ''}
            → {a a' : A}
            → (p : a ≡ a') (f : B → C a)
            → subst (λ - → B → C -) p f ≡ subst C p ∘ f
subst-fun-r refl f = refl

subst-fun-l : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : A → Type ℓ'} {C : Type ℓ''}
            → {a a' : A}
            → (p : a ≡ a') (f : B a → C)
            → subst (λ - → B - → C) p f ≡ f ∘ subst B (sym p)
subst-fun-l refl f = refl

subst-application : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}
                  → (B₁ : A → Type ℓ') {B₂ : A → Type ℓ''}
                  → {x₁ x₂ : A} {y : B₁ x₁}
                  → (g : ∀ x → B₁ x → B₂ x) (p : x₁ ≡ x₂)
                  → subst B₂ p (g x₁ y) ≡ g x₂ (subst B₁ p y)
subst-application _ _ refl = refl

cong-id : ∀ {ℓ} {A : Type ℓ} {a a' : A} → (p : a ≡ a') → cong id p ≡ p
cong-id refl = refl


cong-∘ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {C : Type ℓ''}
       → {a a' : A} → (f : A → B) → (g : B → C)
       → (p : a ≡ a')
       → cong g (cong f p) ≡ cong (λ - → g (f -)) p
cong-∘ f g refl = refl

cong-∙ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
       → {a a' a'' : A} → (f : A → B)
       → (p : a ≡ a') (q : a' ≡ a'')
       → cong f (p ∙ q) ≡ cong f p ∙ cong f q
cong-∙ f refl q = refl

cong-sym : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a a' : A}
         → (f : A → B) (p : a ≡ a')
         → sym (cong f p) ≡ cong f (sym p)
cong-sym f refl = refl

happly-sym : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A -> Type ℓ'} {f g : (a : A) → B a}
           → (p : f ≡ g)
           → sym ∘ happly p ≡ happly (sym p)
happly-sym refl = refl

J : ∀ {ℓ ℓ'} {A : Type ℓ} {x : A} (P : (y : A) → x ≡ y → Type ℓ') → P x refl → {y : A} (p : x ≡ y) → P y p
J P p refl = p

module _ {ℓ} {A : Type ℓ} where
  infixr 2 step-≡ step-≡⁻¹ _≡⟨⟩_
  infix  3 _∎

  step-≡ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ x p q = trans q p

  step-≡⁻¹ : (x : A) {y z : A} → y ≡ z → y ≡ x → x ≡ z
  step-≡⁻¹ x p q = trans (sym q) p

  syntax step-≡ x y p   = x ≡⟨ p ⟩ y
  syntax step-≡⁻¹ x y p = x ≡⟨ p ⟩⁻¹ y

  _≡⟨⟩_ : (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ p = p

  _∎ : (x : A) → x ≡ x
  _ ∎ = refl

record Σ {ℓ ℓ'} (A : Type ℓ) (B : A → Type ℓ') : Type (ℓ ⊔ ℓ') where
  constructor _,_ 
  field
    ₁ : A
    ₂ : B ₁

open Σ public

{-# BUILTIN SIGMA Σ #-}

infixr 4 _,_

infix 5 Σ
syntax Σ A (λ x → B) = Σ[ x ∈ A ] B

infixr 4 _×_
_×_ : ∀ {ℓ ℓ'} (A : Type ℓ) (B : Type ℓ') → Type (ℓ ⊔ ℓ')
_×_ A B = Σ A (λ _ → B)

Σ-≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} → Σ A B → Σ A B → Type (ℓ ⊔ ℓ')
Σ-≡ {B = B} (a , b) (a' , b') = Σ[ eq ∈ a ≡ a' ] (subst B eq b ≡ b')

Σ-≡-assoc : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : A → Set ℓ'} {C : Σ[ x ∈ A ] B x → Set ℓ''}
          → {a a' : A} {b : B a} {b' : B a'} {c : C (a , b)} {c' : C (a' , b')}
          → Σ-≡ ((a , b) , c) ((a' , b') , c')
          → Σ-≡ (a , (b , c)) (a' , (b' , c'))
Σ-≡-assoc (refl , refl) = refl , refl

Σ-≡→≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
      → {x y : Σ A B} → Σ-≡ x y → x ≡ y
Σ-≡→≡  (refl , refl) = refl

≡→Σ-≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
      → {x y : Σ A B} → x ≡ y → Σ-≡ x y
≡→Σ-≡  refl = (refl , refl)

≡→Σ-≡→≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
        → {x y : Σ A B} → (p : x ≡ y) → p ≡ Σ-≡→≡ (≡→Σ-≡ p)
≡→Σ-≡→≡ refl = refl

Σ-≡-sym : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
        → {a₁ a₂ : A} {b₁ : B a₁} {b₂ : B a₂}
        → (p : a₁ ≡ a₂)
        → (q : subst (λ x → B x) p b₁ ≡ b₂)
        → sym (Σ-≡→≡ (p , q)) ≡ Σ-≡→≡ (sym p , sym (cong (subst B (sym p)) q) ∙ subst-sym-l p b₁)
Σ-≡-sym refl refl = refl

subst-Σ : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : Σ[ x ∈ X ] A x → Set ℓ''}
        → {x₁ x₂ : X} {a : A x₁} {b : B (x₁ , a)}
        → (p : x₁ ≡ x₂)
        → subst (λ - → Σ[ a ∈ A - ] (B (- , a))) p (a , b)
        ≡ (subst A p a , subst B (Σ-≡→≡ (p , refl)) b)
subst-Σ refl = refl

subst-Σ' : ∀ {ℓ ℓ' ℓ''} {X : Set ℓ} {A : X → Set ℓ'} {B : Σ[ x ∈ X ] A x → Set ℓ''}
         → {x₁ x₂ : X} {a : A x₁} {a' : A x₂} {b : B (x₁ , a)}
         → (p : x₁ ≡ x₂)
         → (q : subst (λ x → A x) p a ≡ a')
         → subst (λ - → B (x₂ , -)) q (subst B (Σ-≡→≡ (p , refl)) b)
         ≡ subst B (Σ-≡→≡ (p , q)) b
subst-Σ' p refl = refl

data _⊎_ {ℓ} {ℓ'} (A : Type ℓ) (B : Type ℓ') : Type (ℓ ⊔ ℓ') where
  inl : A → A ⊎ B
  inr : B → A ⊎ B


data ℕ : Type where
  zero : ℕ
  suc  : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

pattern 1+ n = suc n
pattern 2+ n = suc (suc n)
pattern 3+ n = suc (suc (suc n))

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)
{-# BUILTIN NATPLUS _+_ #-}

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

+-zero-r : ∀ {n} → n + 0 ≡ n
+-zero-r {zero}  = refl
+-zero-r {suc n} = cong suc +-zero-r

+-suc-r : ∀ {n m} → n + suc m ≡ suc (n + m)
+-suc-r {zero}  = refl
+-suc-r {suc n} = cong suc +-suc-r

+-suc-zero : ∀ n → suc n + zero ≡ suc n
+-suc-zero n = cong suc +-zero-r

+-zero-suc : ∀ n → zero + suc n ≡ suc n
+-zero-suc n = refl

+-suc-suc : ∀ n m → suc n + suc m ≡ suc (suc (n + m))
+-suc-suc n m = cong suc +-suc-r

+-assoc : ∀ n m o → n + m + o ≡ n + (m + o)
+-assoc zero m o = refl
+-assoc (1+ n) m o = cong suc (+-assoc n m o)

infixl 20 _+_

{-# REWRITE +-zero-r +-suc-r #-}
