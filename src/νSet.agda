open import Prelude

module νSet
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

open import νSet.Base fe fe-≡ arity public
open import νSet.Equiv fe fe-≡ arity public
open import νSet.Face fe fe-≡ arity renaming (Face to νFace; Face-coh to νFace-coh) public
