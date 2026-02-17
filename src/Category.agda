open import Prelude

module Category  (arity : Type) where

open import HSet
open import Inequalities

data Hom : ℕ → ℕ → Type where
  base : Hom 0 0
  ari-cons : ∀ {p n} → (ε : arity) → Hom p n → Hom p (suc n)
  nil-cons : ∀ {p n} → Hom p n → Hom (suc p) (suc n)

hom-id : ∀ {n} → Hom n n
hom-id {zero}  = base
hom-id {suc n} = nil-cons (hom-id)

restr : ∀ p n → [ p ≤ n ]₂ → arity → Hom n (1+ n)
restr zero        n p≤n ε = ari-cons ε (hom-id)
restr (1+ p) (1+ n) p≤n ε = nil-cons (restr p n (⇓₂ p≤n) ε)

compose : ∀ {p q n} → Hom q n → Hom p q → Hom p n
compose base           f = f
compose (ari-cons ε g) f = ari-cons ε (compose g f)
compose (nil-cons g) (nil-cons f)   = nil-cons (compose g f)
compose (nil-cons g) (ari-cons ε f) = ari-cons ε (compose g f)

compose-idl : ∀ {p n} → (f : Hom p n) → compose (hom-id) f ≡ f
compose-idl base           = refl
compose-idl (ari-cons ε f) = cong (ari-cons ε) (compose-idl f)
compose-idl (nil-cons f)   = cong nil-cons (compose-idl f)

compose-idr : ∀ {p n} → (f : Hom p n) → compose f (hom-id) ≡ f
compose-idr base           = refl
compose-idr (ari-cons ε f) = cong (ari-cons ε) (compose-idr f)
compose-idr (nil-cons f)   = cong nil-cons (compose-idr f)

compose-assoc : ∀ {p q n r} (h : Hom n r) (g : Hom q n) (f : Hom p q)
              → compose h (compose g f) ≡ compose (compose h g) f
compose-assoc base g f = refl
compose-assoc (ari-cons ε h) g f = cong (ari-cons ε) (compose-assoc h g f)
compose-assoc (nil-cons h) (ari-cons ε g) f = cong (ari-cons ε) (compose-assoc h g f)
compose-assoc (nil-cons h) (nil-cons g) (ari-cons ε f) = cong (ari-cons ε) (compose-assoc h g f)
compose-assoc (nil-cons h) (nil-cons g) (nil-cons f) = cong nil-cons (compose-assoc h g f)

compose-restr : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃) 
              → (ε ω : arity)
              → compose (restr p (1+ n) (↑₂ drop₃-2 p≤q≤n) ω) (restr q n (drop₃-1 p≤q≤n) ε)
              ≡ compose (restr (1+ q) (1+ n) (⇑₂ drop₃-1 p≤q≤n) ε) (restr p n (drop₃-2 p≤q≤n) ω)
compose-restr n zero q p≤q≤n ε ω =
  cong (ari-cons ω) (trans (compose-idl (restr q n _ ε)) (sym (compose-idr (restr q n _ ε))))
compose-restr (1+ n) (1+ p) (1+ q) p≤q≤n ε ω =
  cong nil-cons (compose-restr n p q (⇓₃ p≤q≤n) ε ω)

record RestrInfo (n : ℕ) : Type where
  constructor info
  field
    restr-p : ℕ
    restr-ε : arity
    restr-p≤n : [ restr-p ≤ n ]₂
open RestrInfo public

decompose : ∀ p n → Hom p n
          → (p ≡ n) ⊎ (Σ[ i ∈ RestrInfo p ] Hom (suc p) n)
decompose p n base = inl refl
decompose p n (ari-cons ε f) = inr (info 0 ε (ineq₂ p (≡ℕ-refl p)) , (nil-cons f))
decompose p n (nil-cons f)   with decompose _ _ f
... | inl eq                   = inl (cong suc eq)
... | inr (info p' ε p≤q , f') = inr ((info (1+ p') ε (⇑₂ p≤q)) , (nil-cons f'))

makeF1-aux : (F0 : ℕ → Type)
           → (restr : ∀ (p n : ℕ) → [ p ≤ n ]₂ → arity → F0 (suc n) → F0 n)
           → ∀ p n δ → .(p + δ ≡ℕ n) → Hom p n → F0 n → F0 p
makeF1-aux F0 restr p n zero eq f X with recover-nat-eq' p n eq
... | refl = X
makeF1-aux F0 restr p n (1+ δ) eq f X with decompose p n f
... | inl refl = X
... | inr (info p' ε p≤n , f') =
 restr p' p p≤n ε (makeF1-aux F0 restr (1+ p) n δ eq f' X)

record Presheaf : Type₁ where
  field
    F0 : ℕ → HSet
    F1 : ∀ {p n} → Hom p n → F0 n .Dom → F0 p .Dom
    F1-id : ∀ n → (X : F0 n .Dom) → F1 (hom-id) X ≡ X
    F1-compose : ∀ (p q n : ℕ) (g : Hom q n) (f : Hom p q) (X : F0 n .Dom)
               → F1 f (F1 g X)
               ≡ F1 (compose g f ) X
open Presheaf public

record Presheaf' : Type₁ where
  field
    F0 : ℕ → HSet
    Face : ∀ (n p : ℕ) → [ p ≤ n ]₂ → arity → F0 (1+ n) .Dom → F0 n .Dom
    Face-coh : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃) 
             → (ε ω : arity)
             → (X : F0 (2+ n) .Dom)
             → Face n q (drop₃-1 p≤q≤n) ε (Face (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω X) 
             ≡ Face n p (drop₃-2 p≤q≤n) ω (Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε X)
open Presheaf' public
