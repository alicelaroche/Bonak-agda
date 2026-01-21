module Prelude where

open import Agda.Primitive renaming (Set to Type) public

data ⊥ : Type where

record ⊤ {ℓ} : Type ℓ where
  instance constructor tt
{-# BUILTIN UNIT ⊤ #-}

infix 4 _≡_
data _≡_ {ℓ} {A : Type ℓ} (x : A) : A → Type ℓ where
  refl : x ≡ x
{-# BUILTIN EQUALITY _≡_  #-}
{-# BUILTIN REWRITE _≡_  #-}

module _ {ℓ} {A : Type ℓ} where
  infixr 2 step-≡ step-≡⁻¹ _≡⟨⟩_
  infix  3 _∎

  step-≡ : (x : A) {y z : A} → y ≡ z → x ≡ y → x ≡ z
  step-≡ _ p refl = p

  step-≡⁻¹ : (x : A) {y z : A} → y ≡ z → y ≡ x → x ≡ z
  step-≡⁻¹ _ p refl = p

  syntax step-≡ x y p   = x ≡⟨ p ⟩ y
  syntax step-≡⁻¹ x y p = x ≡⟨ p ⟩⁻¹ y

  _≡⟨⟩_ : (x : A) {y : A} → x ≡ y → x ≡ y
  _ ≡⟨⟩ p = p

  _∎ : (x : A) → x ≡ x
  _ ∎ = refl

sym : ∀ {ℓ} {A : Type ℓ} {a a' : A} → a ≡ a' → a' ≡ a
sym refl = refl

trans : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p refl = p

cong : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {a a' : A} → (f : A → B)
     → a ≡ a' → f a ≡ f a'
cong f refl = refl

cong-app : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A -> Type ℓ'} {f g : (a : A) → B a}
         → f ≡ g → (a : A) → f a ≡ g a
cong-app refl a = refl

subst : ∀ {ℓ ℓ'} {A : Type ℓ} (B : A → Type ℓ') {a a' : A} → a ≡ a' → B a → B a'
subst B refl b = b

subst-sym-l : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a a' : A}
          → (H : a ≡ a') (b : B a)
          → subst B (sym H) (subst B H b) ≡ b
subst-sym-l refl b = refl

subst-sym-r : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {a a' : A}
          → (H : a ≡ a') (b : B a')
          → subst B H (subst B (sym H) b) ≡ b
subst-sym-r refl b = refl

subst-∘ : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {B : Type ℓ'} {x y : A} {C : B → Type ℓ''}
        → {f : A → B}
        → (x≡y : x ≡ y) {p : C (f x)}
        → subst (λ - → C (f -)) x≡y p ≡ subst C (cong f x≡y) p
subst-∘ refl = refl

subst-application : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ}
                  → (B₁ : A → Type ℓ') {B₂ : A → Type ℓ''}
                  → {x₁ x₂ : A} {y : B₁ x₁}
                  → (g : ∀ x → B₁ x → B₂ x) (eq : x₁ ≡ x₂)
                  → subst B₂ eq (g x₁ y) ≡ g x₂ (subst B₁ eq y)
subst-application _ _ refl = refl

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

Σ-≡ : {A : Type} {B : A → Type} → Σ A B → Σ A B → Type
Σ-≡ {B = B} (a , b) (a' , b') = Σ[ eq ∈ a ≡ a' ] (subst B eq b ≡ b')

Σ-≡→≡ : {A : Type} {B : A → Type} {x y : Σ A B} → Σ-≡ x y → x ≡ y
Σ-≡→≡  (refl , refl) = refl 

≡→Σ-≡ : {A : Type} {B : A → Type} {x y : Σ A B} → x ≡ y → Σ-≡ x y
≡→Σ-≡  refl = (refl , refl)

≡→Σ-≡→≡ : {A : Type} {B : A → Type} {x y : Σ A B} → (p : x ≡ y)
        → p ≡ Σ-≡→≡ (≡→Σ-≡ p)
≡→Σ-≡→≡ refl = refl

subst-Σ : {X : Set} {A : X → Set} {B : Σ[ x ∈ X ] A x → Set} {x₁ x₂ : X} {a : A x₁} {b : B (x₁ , a)}
        → (p : x₁ ≡ x₂)
        → subst (λ - → Σ[ a ∈ A - ] (B (- , a))) p (a , b)
        ≡ (subst A p a , subst B (Σ-≡→≡ (p , refl)) b)
subst-Σ refl = refl

subst-Σ' : {X : Set} {A : X → Set} {B : Σ[ x ∈ X ] A x → Set} {x₁ x₂ : X} {a : A x₁} {a' : A x₂} {b : B (x₁ , a)}
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

nat-dec-eq : ∀ {n m : ℕ} → (n ≡ m) ⊎ (n ≡ m → ⊥)
nat-dec-eq {zero} {zero} = inl refl
nat-dec-eq {zero} {suc m} = inr λ ()
nat-dec-eq {suc n} {zero} = inr λ ()
nat-dec-eq {suc n} {suc m} with nat-dec-eq {n} {m}
... | inl eq  = inl (cong suc eq)
... | inr ¬eq = inr λ eq → ¬eq (cong pred eq)


+-suc-r : ∀ {n m} → n + suc m ≡ suc (n + m)
+-suc-r {zero}  = refl
+-suc-r {suc n} = cong suc +-suc-r

⇑_ : ∀ {n m} → n ≡ m → suc n ≡ suc m
⇑ refl = refl

⇓_ : ∀ {n m} → suc n ≡ suc m → n ≡ m
⇓ refl = refl

←_ : ∀ {n m p} → n + suc m ≡ p → suc n + m ≡ p
←_ eq = trans (sym +-suc-r) eq

⇒_ : ∀ {n m p} → suc n + m ≡ p → n + suc m ≡ p 
⇒_ eq = trans +-suc-r eq

infixl 20 _+_

data _≤_ : ℕ → ℕ → Type where
  0≤n : ∀ {n} → 0 ≤ n
  s≤s : ∀ {n m} → n ≤ m → suc n ≤ suc m

◆_ : ∀ n → n ≤ n
◆ zero = 0≤n
◆ 1+ n = s≤s (◆ n)

↑_ : ∀ {n m} → n ≤ m → n ≤ suc m
↑ 0≤n = 0≤n
↑ s≤s n≤m = s≤s (↑ n≤m)

↑[_]_ : ∀ {n m} → (k : ℕ) → n ≤ m → n ≤ (m + k)
↑[ k ] 0≤n = 0≤n
↑[ k ] s≤s m≤n = s≤s (↑[ k ] m≤n)

↓↓_ : ∀ {n m} → suc n ≤ suc m → n ≤ m
↓↓ s≤s n≤m = n≤m

_↕_ : ∀ {n m p} → n ≤ m → m ≤ p → n ≤ p
0≤n ↕ m≤p = 0≤n
s≤s n≤m ↕ s≤s m≤p = s≤s (n≤m ↕ m≤p)

contradiction-irr : ∀ {ℓ} {A : Type ℓ} → .⊥ → A
contradiction-irr ()

irr-recover : ∀ {ℓ} {A : Type ℓ} → A ⊎ (A → ⊥) → .A → A
irr-recover (inl a)  _ = a
irr-recover (inr ¬a) a = contradiction-irr (¬a a)

opaque
  recover-nat-eq : ∀ {n m : ℕ} → .(n ≡ m) → n ≡ m
  recover-nat-eq = irr-recover nat-dec-eq
