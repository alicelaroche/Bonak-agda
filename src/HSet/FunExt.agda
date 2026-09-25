open import Prelude
open import HSet.Base
open import Axioms.FunExt

module HSet.FunExt
 (fe : FunExt-Axiom)
 where
 open FE fe

 isProp-isProp : ∀ {ℓ} {A : Type ℓ} → isProp (isProp A)
 isProp-isProp x y = funExt λ p → funExt λ q → isProp→UIP x p q (x p q) (y p q)

 UIP-isProp : ∀ {ℓ} {A : Type ℓ} → isProp (UIP A)
 UIP-isProp x y = funExt λ a → funExt λ a' → isProp-isProp (x a a') (y a a')

 HSet-≡ : (A B : HSet) → A .Dom ≡ B .Dom → A ≡ B
 HSet-≡ (hset A has-UIP) (hset .A has-UIP') refl =
   cong (hset A) (UIP-isProp has-UIP has-UIP')

 HSet-≡-sym : ∀ (A B : HSet)
            → (p : A .Dom ≡ B .Dom)
            → sym (HSet-≡ A B p) ≡ HSet-≡ B A (sym p)
 HSet-≡-sym (hset A has-UIP) (hset _ has-UIP') refl =
   sym (cong (hset A) (UIP-isProp has-UIP has-UIP'))
     ≡⟨ cong-sym (hset A) (UIP-isProp has-UIP has-UIP') ⟩
   cong (hset A) (sym (UIP-isProp has-UIP has-UIP'))
     ≡⟨ cong (cong (hset A)) (isProp→UIP UIP-isProp _ _ _ _) ⟩
   cong (hset A) (UIP-isProp has-UIP' has-UIP) ∎

 HSet-≡-subst : ∀ {ℓ} (A B : HSet) {C : Type → Type ℓ}
              → (p : A .Dom ≡ B .Dom) {c : C (A .Dom)}
              → subst (λ - → C (- .Dom)) (HSet-≡ A B p) c
              ≡ subst C p c
 HSet-≡-subst (hset A has-UIP) (hset _ has-UIP') {C} refl {c} =
    subst (λ - → C (- .Dom)) (cong (hset A) (UIP-isProp has-UIP has-UIP')) c
      ≡⟨ subst-∘ (UIP-isProp has-UIP has-UIP') c ⟩⁻¹
    subst (λ - → C ((hset A -) .Dom)) (UIP-isProp has-UIP has-UIP') c
      ≡⟨⟩
    subst (λ - → C A) (UIP-isProp has-UIP has-UIP') c
      ≡⟨ subst-const _ c ⟩
    c ∎ 
  
 Π-is-set : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} (B-is-set : ∀ x → UIP (B x))
          → UIP ((x : A) → B x)
 Π-is-set B-is-set a a' p q =
  p
   ≡⟨ funExt-η p ⟩⁻¹
  funExt (λ a → happly p a)
   ≡⟨ cong funExt (funExt λ a → B-is-set a _ _ _ _) ⟩
  funExt (λ a → happly q a)
   ≡⟨ funExt-η q ⟩
  q ∎

 HΠ : (A : Type) (B : A → HSet) → HSet
 HΠ A B .Dom = (x : A) → (B x .Dom)
 HΠ A B .has-UIP =  Π-is-set (λ - → B - .has-UIP)

 HΠ-syntax : (A : Type) (B : A → HSet) → HSet
 HΠ-syntax = HΠ

 infix 2 HΠ-syntax
 syntax HΠ-syntax A (λ x → B) = HΠ[ x ∈ A ] B

