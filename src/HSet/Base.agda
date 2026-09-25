open import Prelude

module HSet.Base where

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

opaque
  ℕ-UIP : UIP ℕ
  ℕ-UIP (zero) (zero) refl refl = refl
  ℕ-UIP (1+ x) (1+ y) p q =
   p ≡⟨ ℕ-cong p ⟩⁻¹
   cong suc (cong pred p) ≡⟨ cong (cong suc) (ℕ-UIP x y (cong pred p) (cong pred q)) ⟩
   cong suc (cong pred q) ≡⟨ ℕ-cong q ⟩
   q ∎

  Σ-UIP : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
        → (A-is-set : UIP A)
        → (B-is-set : (a : A) → UIP (B a))
        → UIP (Σ A B)
  Σ-UIP A-is-set B-is-set x y p q =
    p               ≡⟨ ≡→Σ-≡→≡ p ⟩
    Σ-≡→≡ (≡→Σ-≡ p) ≡⟨ cong Σ-≡→≡ (Σ-≡→≡ ((A-is-set _ _ _ _) , (B-is-set _ _ _ _ _))) ⟩
    Σ-≡→≡ (≡→Σ-≡ q) ≡⟨ ≡→Σ-≡→≡ q ⟩⁻¹
    q ∎


  IVec-UIP : ∀ {ℓ} (n : ℕ) {A : Fin n → Type ℓ}
           → (∀ i → UIP (A i))
           → UIP (IVec n A)
  IVec-UIP zero A-is-set _ _ refl refl = refl
  IVec-UIP (1+ n) A-is-set = Σ-UIP (IVec-UIP n λ i → A-is-set (𝐒 i)) (λ _ → A-is-set 𝟎)

record HSet : Type₁ where
 constructor hset
 field
  Dom : Type
  has-UIP : UIP Dom

open HSet public

HUnit : HSet
HUnit .Dom = ⊤
HUnit .has-UIP _ _ refl refl = refl

HΣ : (A : HSet) (B : A .Dom → HSet) → HSet
HΣ A B .Dom = Σ[ a ∈ A .Dom ] (B a .Dom)
HΣ A B .has-UIP = Σ-UIP (A .has-UIP) (λ a → B a .has-UIP)

HΣ-syntax : (A : HSet) (B : A .Dom → HSet) → HSet
HΣ-syntax = HΣ

HIVec : (n : ℕ) → (A : Fin n → HSet) → HSet
HIVec n A .Dom = IVec n (λ i → A i .Dom)
HIVec n A .has-UIP = IVec-UIP n (λ i → A i .has-UIP)

H≡ : (A : HSet) → (x y : A .Dom) → HSet
H≡ A x y .Dom = x ≡ y
H≡ A x y .has-UIP = isProp→UIP (A .has-UIP x y)

infix 2 HΣ-syntax
syntax HΣ-syntax A (λ x → B) = HΣ[ x ∈ A ] B
