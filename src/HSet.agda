open import Prelude

module HSet where

isContr : ∀ {ℓ} (A : Type ℓ) → Type ℓ 
isContr A = Σ[ x ∈ A ] (∀ y → x ≡ y)

isProp : ∀ {ℓ} (A : Type ℓ) → Type ℓ 
isProp A = (x y : A) → x ≡ y

UIP : ∀ {ℓ} (A : Type ℓ) → Type ℓ
UIP A = ∀ (a a' : A) (p q : a ≡ a') → p ≡ q

isContr→isContrPath : ∀ {ℓ} {A : Type ℓ}
                    → isContr A
                    → (x y : A) → isContr (x ≡ y)
isContr→isContrPath (x , f) y z = (trans (sym (f y)) (f z)) , I
 where
 I : (q : y ≡ z) → trans (sym (f y)) (f z) ≡ q
 I refl = trans-sym-l (f y)

isContr→isProp : ∀ {ℓ} {A : Type ℓ}
               → isContr A
               → isProp A
isContr→isProp (x , f) y z = trans (sym (f y)) (f z)

isProp→isContrPath : ∀ {ℓ} {A : Type ℓ}
                   → isProp A
                   → (x y : A) → isContr (x ≡ y)
isProp→isContrPath f a a' = isContr→isContrPath (a , (f a)) a a'

isProp→UIP : ∀ {ℓ} {A : Type ℓ} → isProp A → UIP A
isProp→UIP propA a a' = isContr→isProp (isProp→isContrPath propA _ _)

ℕ-cong : ∀ {n m} (p : 1+ n ≡ 1+ m) → cong suc (cong pred p) ≡ p
ℕ-cong refl = refl

ℕ-UIP : UIP ℕ
ℕ-UIP (zero) (zero) refl refl = refl
ℕ-UIP (1+ x) (1+ y) p q =
 p ≡⟨ ℕ-cong p ⟩⁻¹
 cong suc (cong pred p) ≡⟨ cong (cong suc) (ℕ-UIP x y (cong pred p) (cong pred q)) ⟩
 cong suc (cong pred q) ≡⟨ ℕ-cong q ⟩
 q ∎

Σ-UIP : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
      → (A-is-set : UIP A)
      → (B-is-set : (a : A) → UIP (B a))
      → UIP (Σ A B)
Σ-UIP A-is-set B-is-set x y p q =
  p               ≡⟨ ≡→Σ-≡→≡ p ⟩
  Σ-≡→≡ (≡→Σ-≡ p) ≡⟨ cong Σ-≡→≡ (Σ-≡→≡ ((A-is-set _ _ _ _) , (B-is-set _ _ _ _ _))) ⟩
  Σ-≡→≡ (≡→Σ-≡ q) ≡⟨ ≡→Σ-≡→≡ q ⟩⁻¹
  q ∎

record HSet : Type₁ where
 constructor hset
 field
  Dom : Type
  has-UIP : UIP Dom

open HSet public

module _
 (fe : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
     → (f g : (a : A) → B a)
     → (∀ a → f a ≡ g a)
     → f ≡ g)
 where

  UIP-isProp : ∀ {ℓ} {A : Type ℓ}
             → isProp (UIP A)
  UIP-isProp x y =
   fe x y λ a → fe _ _ λ a' → fe _ _ λ p → fe _ _ λ q →
     (isProp→UIP (x a a') p q (x a a' p q) (y a a' p q))

  HSet-≡ : (A B : HSet) → A .Dom ≡ B .Dom → A ≡ B
  HSet-≡ (hset A has-UIP) (hset .A has-UIP') refl =
    cong (hset A) (UIP-isProp has-UIP has-UIP')

HUnit : HSet
HUnit .Dom = ⊤
HUnit .has-UIP _ _ refl refl = refl

HΣ : (A : HSet) (B : A .Dom → HSet) → HSet
HΣ A B .Dom = Σ[ a ∈ A .Dom ] (B a .Dom)
HΣ A B .has-UIP = Σ-UIP (A .has-UIP) (λ a → B a .has-UIP)

HΣ-syntax : (A : HSet) (B : A .Dom → HSet) → HSet
HΣ-syntax = HΣ

H≡ : (A : HSet) → (x y : A .Dom) → HSet
H≡ A x y .Dom = x ≡ y
H≡ A x y .has-UIP = isProp→UIP (A .has-UIP x y)

infix 2 HΣ-syntax
syntax HΣ-syntax A (λ x → B) = HΣ[ x ∈ A ] B

module HΠ
 (fe : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
     → (f g : (a : A) → B a)
     → (∀ a → f a ≡ g a)
     → f ≡ g)
 (fe-≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
       → (f g : (a : A) → B a)
       → (p : f ≡ g)
       → fe f g (λ a → cong-app p a) ≡ p)
 where

 Π-is-set : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (B-is-set : ∀ x → UIP (B x))
          → UIP ((x : A) → B x)
 Π-is-set B-is-set a a' p q =
  p
   ≡⟨ fe-≡ _ _ p ⟩⁻¹
  fe _ _ (λ a → cong-app p a)
   ≡⟨ cong (fe _ _) (fe _ _ λ a → B-is-set a _ _ _ _) ⟩
  fe _ _ (λ a → cong-app q a)
   ≡⟨ fe-≡ _ _ q ⟩
  q ∎

 HΠ : (A : Set) (B : A → HSet) → HSet
 HΠ A B .Dom = (x : A) → (B x .Dom)
 HΠ A B .has-UIP =  Π-is-set (λ - → B - .has-UIP)

 HΠ-syntax : (A : Type) (B : A → HSet) → HSet
 HΠ-syntax = HΠ

 infix 2 HΠ-syntax
 syntax HΠ-syntax A (λ x → B) = HΠ[ x ∈ A ] B


open HΠ
