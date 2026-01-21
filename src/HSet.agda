open import Prelude

module HSet where

UIP : ∀ {ℓ} (A : Type ℓ) → Type ℓ
UIP A = ∀ {a a' : A} (p q : a ≡ a') → p ≡ q

record HSet : Type₁ where
 field
  Dom : Type
  has-UIP : UIP Dom

open HSet public

HUnit : HSet
HUnit .Dom = ⊤
HUnit .has-UIP refl refl = refl

ℕ-cong : ∀ {n m} (p : 1+ n ≡ 1+ m) → cong suc (cong pred p) ≡ p
ℕ-cong refl = refl

ℕ-UIP : UIP ℕ
ℕ-UIP {zero} {zero} refl refl = refl
ℕ-UIP {1+ x} {1+ y} p q =
 p ≡⟨ ℕ-cong p ⟩⁻¹
 cong suc (cong pred p) ≡⟨ cong (cong suc) (ℕ-UIP {x} {y} (cong pred p) (cong pred q)) ⟩
 cong suc (cong pred q) ≡⟨ ℕ-cong q ⟩
 q ∎

Σ-UIP : {A : Set} {B : A → Set}
      → (A-is-set : UIP A)
      → (B-is-set : (a : A) → UIP (B a))
      → UIP (Σ A B)
Σ-UIP A-is-set B-is-set {x} {y} p q =
  p               ≡⟨ ≡→Σ-≡→≡ p ⟩
  Σ-≡→≡ (≡→Σ-≡ p) ≡⟨ cong Σ-≡→≡ (Σ-≡→≡ ((A-is-set _ _) , (B-is-set _ _ _))) ⟩
  Σ-≡→≡ (≡→Σ-≡ q) ≡⟨ ≡→Σ-≡→≡ q ⟩⁻¹
  q ∎

HΣ : (A : HSet) (B : A .Dom → HSet) → HSet
HΣ A B .Dom = Σ[ a ∈ A .Dom ] (B a .Dom)
HΣ A B .has-UIP = Σ-UIP (A .has-UIP) (λ a → B a .has-UIP)

HΣ-syntax : (A : HSet) (B : A .Dom → HSet) → HSet
HΣ-syntax = HΣ

infix 2 HΣ-syntax
syntax HΣ-syntax A (λ x → B) = HΣ[ x ∈ A ] B

module HΠ
 (fe : {A : Type} {B : A → Type}
     → (f g : (a : A) → B a)
     → (∀ a → f a ≡ g a)
     → f ≡ g)
 (fe-≡ : {A : Set} {B : A → Set}
       → (f g : (a : A) → B a)
       → (p : f ≡ g)
       → fe f g (λ a → cong-app p a) ≡ p)
 where

 Π-is-set : {A : Set} {B : A → Set} (B-is-set : ∀ x → UIP (B x))
          → UIP ((x : A) → B x)
 Π-is-set B-is-set p q =
  p
   ≡⟨ fe-≡ _ _ p ⟩⁻¹
  fe _ _ (λ a → cong-app p a)
   ≡⟨ cong (fe _ _) (fe _ _ λ a → B-is-set a _ _) ⟩
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
