open import Prelude

module Category  (arity : Type) where

open import HSet

data Hom : ℕ → ℕ → Type where
  base : Hom 0 0
  ari-cons : ∀ {p n} → (ε : arity) → Hom p n → Hom p (suc n)
  nil-cons : ∀ {p n} → Hom p n → Hom (suc p) (suc n)

id : ∀ {n} → Hom n n
id {zero}  = base
id {suc n} = nil-cons id

compose : ∀ {p q n} → Hom q n → Hom p q → Hom p n
compose base           f = f
compose (ari-cons ε g) f = ari-cons ε (compose g f)
compose (nil-cons g) (nil-cons f)   = nil-cons (compose g f)
compose (nil-cons g) (ari-cons ε f) = ari-cons ε (compose g f)

compose-idl : ∀ {p n} → (f : Hom p n) → compose id f ≡ f
compose-idl base           = refl
compose-idl (ari-cons ε f) = cong (ari-cons ε) (compose-idl f)
compose-idl (nil-cons f)   = cong nil-cons (compose-idl f)

compose-idr : ∀ {p n} → (f : Hom p n) → compose f id ≡ f
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

makeF1-aux : (k : ℕ)
           → (F0 : ℕ → Type)
           → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) → F0 n)
           → ∀ {p n} → Hom p n → F0 (k + n) → F0 (k + p)
makeF1-aux k F0 restr base X = X
makeF1-aux k F0 restr {p} {n} (ari-cons ε f) X =
  restr k (k + p) ε (↑[ p ] (◆ k)) (makeF1-aux (suc k) F0 restr f X)
makeF1-aux k F0 restr (nil-cons f) X = makeF1-aux (suc k) F0 restr f X


makeF1-aux-id : ∀ k
  → (F0 : ℕ → Type)
  → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) → F0 n)
  → ∀ (n : ℕ) (X : F0 (k + n))
  → makeF1-aux k F0 restr (id {n}) X ≡ X
makeF1-aux-id k F0 restr zero X   = refl
makeF1-aux-id k F0 restr (1+ n) X = makeF1-aux-id (1+ k) F0 restr n X

makeF1-aux-compose-helper : ∀ k k' → .(k'≤k : k' ≤ k)
  → (F0 : ℕ → Type)
  → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) → F0 n)
  → (restr-correct : ∀ p q n → .(Hp : p ≤ q) → .(Hq : q ≤ n) → (ε ω : arity)
                             → (X : F0 (suc (suc n)))
                             → restr p n ε (Hp ↕ Hq) (restr (suc q) (suc n) ω (s≤s Hq) X)
                             ≡ restr q n ω Hq (restr p (suc n) ε (↑ (Hp ↕ Hq)) X))
  → ∀ (p n : ℕ) (ε : arity) (f : Hom p n) (X : F0 (suc k + n))
  → makeF1-aux k F0 restr f (restr k' (k + n) ε (↑[ n ] k'≤k) X)
  ≡ restr k' (k + p) ε (↑[ p ] k'≤k) (makeF1-aux (suc k) F0 restr f X)
makeF1-aux-compose-helper k k' k'≤k F0 restr restr-correct p n ε base X = refl
makeF1-aux-compose-helper k k' k'≤k F0 restr restr-correct p (1+ n) ε (ari-cons ω f) X =
  restr k (k + p) ω _
    (makeF1-aux (1+ k) F0 restr f (restr k' (1+ (k + n)) ε _ X))
    ≡⟨ cong (restr k (k + p) ω _)
        (makeF1-aux-compose-helper (1+ k) k' (↑ k'≤k) F0 restr restr-correct p n ε f _) ⟩
  restr k (k + p) ω _
    (restr k' (1+ k + p) ε _ (makeF1-aux (2+ k) F0 restr f X))
    ≡⟨ restr-correct k' k (k + p) k'≤k (↑[ p ] (◆ k)) ε ω _ ⟩⁻¹
  restr k' (k + p) ε _
    (restr (1+ k) (1+ (k + p)) ω _ (makeF1-aux (2+ k) F0 restr f X)) ∎ 
makeF1-aux-compose-helper k k' k'≤k F0 restr restr-correct (1+ p) (1+ n) ε (nil-cons f) X =
  makeF1-aux-compose-helper (1+ k) k' (↑ k'≤k) F0 restr restr-correct p n ε f _

makeF1-aux-compose : ∀ k
  → (F0 : ℕ → Type)
  → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) → F0 n)
  → (restr-correct : ∀ p q n → .(Hp : p ≤ q) → .(Hq : q ≤ n) → (ε ω : arity)
                             → (X : F0 (suc (suc n)))
                             → restr p n ε (Hp ↕ Hq) (restr (suc q) (suc n) ω (s≤s Hq) X)
                             ≡ restr q n ω Hq (restr p (suc n) ε (↑ (Hp ↕ Hq)) X))
  → ∀ (p q n : ℕ) (g : Hom q n) (f : Hom p q) (X : F0 (k + n))
  → makeF1-aux k F0 restr f (makeF1-aux k F0 restr g X) ≡
    makeF1-aux k F0 restr (compose g f ) X
makeF1-aux-compose k F0 restr restr-correct p q n base f X = refl
makeF1-aux-compose k F0 restr restr-correct p q n (ari-cons ε g) f X =
  makeF1-aux k F0 restr f
    (restr k (k + q) ε _ (makeF1-aux (1+ k) F0 restr g X))
    ≡⟨ makeF1-aux-compose-helper k k (◆ k) F0 restr restr-correct p q ε f _ ⟩
  restr k (k + p) ε _ (makeF1-aux (1+ k) F0 restr f (makeF1-aux (1+ k) F0 restr g X))
    ≡⟨ cong (restr k (k + p) ε _) (makeF1-aux-compose (1+ k) F0 restr restr-correct p q _ g f _) ⟩
  restr k (k + p) ε _ (makeF1-aux (1+ k) F0 restr (compose g f) X) ∎
makeF1-aux-compose k F0 restr restr-correct p (1+ q) (1+ n) (nil-cons g) (ari-cons ε f) X =
  cong (restr k (k + p) ε _) (makeF1-aux-compose (1+ k) F0 restr restr-correct p q n g f X)
makeF1-aux-compose k F0 restr restr-correct (1+ p) (1+ q) (1+ n) (nil-cons g) (nil-cons f) X =
  makeF1-aux-compose (1+ k) F0 restr restr-correct p q n g f _

makeF1 : (F0 : ℕ → Type)
       → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) → F0 n)
       → ∀ {p n} → Hom p n → F0 n → F0 p
makeF1 = makeF1-aux 0

makeF1-id :
  ∀ (F0 : ℕ → Type)
  → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) → F0 n)
  → ∀ (n : ℕ) (X : F0 n)
  → makeF1 F0 restr id X ≡ X
makeF1-id = makeF1-aux-id 0

makeF1-compose :
  ∀ (F0 : ℕ → Type)
  → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) → F0 n)
  → (restr-correct : ∀ p q n → .(Hp : p ≤ q) → .(Hq : q ≤ n) → (ε ω : arity)
                             → (X : F0 (suc (suc n)))
                             → restr p n ε (Hp ↕ Hq) (restr (suc q) (suc n) ω (s≤s Hq) X)
                             ≡ restr q n ω Hq (restr p (suc n) ε (↑ (Hp ↕ Hq)) X))
  → ∀ (p q n : ℕ) (g : Hom q n) (f : Hom p q) (X : F0 n)
  → makeF1 F0 restr f (makeF1 F0 restr g X) ≡
    makeF1 F0 restr (compose g f ) X
makeF1-compose = makeF1-aux-compose 0

record Presheaf : Type₁ where
  field
    F0 : ℕ → HSet
    F1 : ∀ {p n} → Hom p n → F0 n .Dom → F0 p .Dom
    F1-id : ∀ n → (X : F0 n .Dom) → F1 id X ≡ X
    F1-compose : ∀ (p q n : ℕ) (g : Hom q n) (f : Hom p q) (X : F0 n .Dom)
               → F1 f (F1 g X)
               ≡ F1 (compose g f ) X
open Presheaf

makePresheaf : (F0 : ℕ → HSet)
             → (restr : ∀ (p n : ℕ) → arity → .(p ≤ n) → F0 (suc n) .Dom → F0 n .Dom)
             → (restr-correct : ∀ p q n → .(Hp : p ≤ q) → .(Hq : q ≤ n) → (ε ω : arity)
                             → (X : F0 (suc (suc n)) .Dom)
                             → restr p n ε (Hp ↕ Hq) (restr (suc q) (suc n) ω (s≤s Hq) X)
                             ≡ restr q n ω Hq (restr p (suc n) ε (↑ (Hp ↕ Hq)) X)) 
             → Presheaf
makePresheaf F0 restr restr-correct .F0 = F0
makePresheaf F0 restr restr-correct .F1 = makeF1 _ restr
makePresheaf F0 restr restr-correct .F1-id = makeF1-id _ restr
makePresheaf F0 restr restr-correct .F1-compose = makeF1-compose _ restr restr-correct
