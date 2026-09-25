open import Prelude
open import HSet.Base
open import νSet.Context

module νSet.Coh-Frame
  (arity : ℕ)
 where

open import νSet.Frame arity
open import νSet.Painting arity
open import νSet.Restr-Frame arity
open import νSet.Restr-Painting arity

coh₂ : ∀ {A : HSet} {B : A .Dom → Type}
     → {a a₁ a₁' a₂ a₂' a' : A .Dom} {b : B a}
     → (H₁ : a₁' ≡ a') (H₁' : a₁ ≡ a₁') (H₁'' : a ≡ a₁)
       (H₂ : a₂' ≡ a') (H₂' : a₂ ≡ a₂') (H₂'' : a ≡ a₂)
     → subst B H₁ (
       subst B H₁' (
       subst B H₁'' b))
     ≡ subst B H₂ (
       subst B H₂' (
       subst B H₂'' b))
coh₂ {A} {B} {b = b} refl refl refl refl refl H₂'' =
 cong (λ - → subst B - b) (A .has-UIP _ _ refl H₂'')

record DepsCoh₂ (p δ : ℕ) : Type₁ where
 eta-equality
 constructor mkCoh₂Deps
 field
  deps-coh : DepsCoh p δ
  ext-coh : full deps-coh
  coh-painting : coh-PAINTING p δ deps-coh ext-coh
open DepsCoh₂ public

coh-frame-next : ∀ p δ → (deps-coh₂ : DepsCoh₂ p δ)
               → coh-FRAME (1+ p) δ
                  (deps-next (deps-coh₂ .deps-coh))
                  (depsFull-next (deps-coh₂ .deps-coh) (deps-coh₂ .ext-coh))
                  (restr-painting-next _ _ (deps-coh₂ .deps-coh) (deps-coh₂ .ext-coh))

deps-coh-next : ∀ {p δ} → DepsCoh₂ p δ → DepsCoh (1+ p) δ
deps-coh-next deps-coh₂ .deps = deps-next (deps-coh₂ .deps-coh)
deps-coh-next deps-coh₂ .ext = depsFull-next (deps-coh₂ .deps-coh) (deps-coh₂ .ext-coh)
deps-coh-next deps-coh₂ .restr-painting = restr-painting-next _ _ (deps-coh₂ .deps-coh) (deps-coh₂ .ext-coh)
deps-coh-next deps-coh₂ .coh-frame = coh-frame-next _ _ deps-coh₂

instance
  depsCoh₂ContextFst : ContextFst DepsCoh₂
  depsCoh₂ContextFst .fst deps = mkCoh₂Deps (fst (deps .deps-coh)) (full-fst (deps .ext-coh)) (deps .coh-painting .₁)
  
coh-layer : ∀ p δ (deps-coh₂ : DepsCoh₂ (1+ p) δ)
          → ∀ q r ε ω (q≤δ : q ≤ δ) (r≤q : r ≤ q)
          → (d : frame-next p (3+ δ) (fst (fst (deps-next (deps-coh-next (fst deps-coh₂))))) .₂ .Dom)
          → (l : layer p (2+ δ) (fst (deps-next (deps-coh-next (fst deps-coh₂)))) d .Dom )
          → subst (λ - → layer p δ (deps-coh₂ .deps-coh .deps) - .Dom)
              (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d)
              (restr-layer p δ (deps-coh₂ .deps-coh) q q≤δ ε _
                 (restr-layer p (1+ δ) (deps-coh-next (fst deps-coh₂)) r (↑ (r≤q ↕ q≤δ)) ω d l))
          ≡ restr-layer p δ (deps-coh₂ .deps-coh) r (r≤q ↕ q≤δ) ω _
             (restr-layer p (1+ δ) (deps-coh-next (fst deps-coh₂)) (1+ q) (s≤s q≤δ) ε d l)
coh-layer p δ deps-coh₂ q r ε ω q≤δ r≤q d l =
 subst (λ - → layer p δ (deps-coh₂ .deps-coh .deps) - .Dom)
   (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d)
   (restr-layer p δ (deps-coh₂ .deps-coh) q q≤δ ε _
     (restr-layer p (1+ δ) (deps-coh-next (fst deps-coh₂)) r (↑ (r≤q ↕ q≤δ)) ω d l))
  ≡⟨ subst-map _ (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d) ⟩
 map (restr-layer p δ (deps-coh₂ .deps-coh) q q≤δ ε _
       (restr-layer p (1+ δ) (deps-coh-next (fst deps-coh₂)) r (↑ (r≤q ↕ q≤δ)) ω d l)) (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ -) .Dom)
   (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d) l)
  ≡⟨ map-comp _ ⟩
 map (restr-layer p (1+ δ) (deps-coh-next (fst deps-coh₂)) r (↑ (r≤q ↕ q≤δ)) ω d l) (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ -) .Dom)
   (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d))
   (deps-coh₂ .deps-coh .restr-painting .₂ q q≤δ ε _ l))) 
  ≡⟨ map-comp l ⟩
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ -) .Dom)
   (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d))
   (deps-coh₂ .deps-coh .restr-painting .₂ q q≤δ ε _ (
 subst (λ - → deps-coh-next (fst deps-coh₂) .deps .painting .₂ - .Dom)
   (deps-coh-next (fst deps-coh₂) .coh-frame .₂ r 0 ω θ _ _ d)
   (deps-coh-next (fst deps-coh₂) .restr-painting .₂ r _ ω _ l)))))
  ≡⟨ map-≡ l (λ θ l →  subst-∘ (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d) _)  ⟩
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ)
     (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d))
   (deps-coh₂ .deps-coh .restr-painting .₂ q q≤δ ε _ (
 subst (λ - → deps-coh-next (fst deps-coh₂) .deps .painting .₂ - .Dom)
   (deps-coh-next (fst deps-coh₂) .coh-frame .₂ r 0 ω θ _ _ d)
   (deps-coh-next (fst deps-coh₂) .restr-painting .₂ r _ ω _ l)))))
  ≡⟨ map-≡ l (λ θ l →
     cong (λ - →
       subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
        (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ)
          (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d)) (
       subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
        (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d)) -))
     (subst-application
       (λ - → deps-coh-next (fst deps-coh₂) .deps .painting .₂ - .Dom)
       (deps-coh₂ .deps-coh .restr-painting .₂ q q≤δ ε)
       (deps-coh-next (fst deps-coh₂) .coh-frame .₂ r 0 ω θ _ _ d))) ⟩⁻¹
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ)
     (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ (deps-coh₂ .deps-coh .deps .restr-frame .₂ q _ ε -) .Dom)
   (deps-coh-next (fst deps-coh₂) .coh-frame .₂ r 0 ω θ _ _ d)
   (deps-coh₂ .deps-coh .restr-painting .₂ q q≤δ ε _
     (deps-coh-next (fst deps-coh₂) .restr-painting .₂ r _ ω _ l)))))
  ≡⟨ map-≡ l (λ θ l →
     cong (λ - →
       subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
        (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ)
          (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d)) (
       subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
        (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d)) -))
     (subst-∘ (deps-coh-next (fst deps-coh₂) .coh-frame .₂ r 0 ω θ _ _ d) _)) ⟩
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ)
     (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ q _ ε)
     (deps-coh-next (fst deps-coh₂) .coh-frame .₂ r 0 ω θ _ _ d))
   (deps-coh₂ .deps-coh .restr-painting .₂ q q≤δ ε _
     (deps-coh-next (fst deps-coh₂) .restr-painting .₂ r _ ω _ l)))))
  ≡⟨ map-≡ l (λ θ l → coh₂ {A = deps-coh₂ .deps-coh .deps .frame .₂}
      (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ 0 0≤n θ)
        (coh-frame-next p (1+ δ) (fst deps-coh₂) .₂ (1+ q) (1+ r) ε ω _ _ d))
      (deps-coh₂ .deps-coh .coh-frame .₂ q 0 ε θ _ _ (restr-frame-next p (2+ δ) _ .₂ (1+ r) _ ω d))
      (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ q _ ε)
        (deps-coh-next (fst deps-coh₂) .coh-frame .₂ r 0 ω θ _ _ d))
      (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ 0≤n (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d))
      (cong (λ - → deps-coh₂ .deps-coh .deps .restr-frame .₂ r _ ω -)
        (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ _ d))
      (deps-coh₂ .deps-coh .coh-frame .₂ q r ε ω _ _ _)) ⟩
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ 0≤n (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (cong (λ - → deps-coh₂ .deps-coh .deps .restr-frame .₂ r _ ω -)
     (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ _ d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ q r ε ω _ _ _)
   (deps-coh₂ .deps-coh .restr-painting .₂ q _ ε _
     (deps-coh-next (fst deps-coh₂) .restr-painting .₂ r _ ω _ l)))))
  ≡⟨ map-≡ l (λ θ l →
     cong (λ - →
       subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
         (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ _ (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d)) (
       subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
         (cong (λ - → deps-coh₂ .deps-coh .deps .restr-frame .₂ r _ ω -)
            (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ 0≤n d))
       -))
     (deps-coh₂ .coh-painting .₂ q r ε ω q≤δ r≤q _ l)) ⟩
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ 0≤n (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (cong (deps-coh₂ .deps-coh .deps .restr-frame .₂ r _ ω)
     (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ _ d))
   (deps-coh₂ .deps-coh .restr-painting .₂ r _ ω _
     (deps-coh-next (fst deps-coh₂) .restr-painting .₂ (1+ q) _ ε _ l))))
  ≡⟨ map-≡ l (λ θ l → 
     cong (subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
            (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ 0≤n (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d)))
    (subst-∘ (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ _ d) _)) ⟩⁻¹
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ 0≤n (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d)) (
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ (deps-coh₂ .deps-coh .deps .restr-frame .₂ r _ ω -) .Dom)
   (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ _ d)
   (deps-coh₂ .deps-coh .restr-painting .₂ r _ ω _
     (deps-coh-next (fst deps-coh₂) .restr-painting .₂ (1+ q) _ ε _ l))))
  ≡⟨ map-≡ l (λ θ l → 
     cong (subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
            (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ 0≤n (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d))) (
     subst-application (λ - → deps-coh-next (fst deps-coh₂) .deps .painting .₂ - .Dom)
       (deps-coh₂ .deps-coh .restr-painting .₂ r _ ω)
       (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ _ d))) ⟩
 map l (λ θ l →
 subst (λ - → deps-coh₂ .deps-coh .deps .painting .₂ - .Dom)
   (deps-coh₂ .deps-coh .coh-frame .₂ r 0 ω θ _ _ (restr-frame-next p (2+ δ) _ .₂ (2+ q) _ ε d))
   (deps-coh₂ .deps-coh .restr-painting .₂ r _ ω _ (
 subst (λ - → deps-coh-next (fst deps-coh₂) .deps .painting .₂ - .Dom)
   (deps-coh-next (fst deps-coh₂) .coh-frame .₂ (1+ q) 0 ε θ _ _ d)
   (deps-coh-next (fst deps-coh₂) .restr-painting .₂ (1+ q) _ ε _ l))))
  ≡⟨ map-comp l ⟩⁻¹
 restr-layer p δ (deps-coh₂ .deps-coh) r (r≤q ↕ q≤δ) ω _
   (restr-layer p (1+ δ) (deps-coh-next (fst deps-coh₂)) (1+ q) (s≤s q≤δ) ε d l) ∎

coh-frame-next zero δ deps-coh₂ = tt , (λ q r ε ω q≤δ r≤q d → refl)
coh-frame-next (1+ p) δ deps-coh₂ =
 let rec = coh-frame-next p (1+ δ) (fst deps-coh₂) in  
 rec , λ q r ε ω q≤δ r≤q (d , l) →
   Σ-≡→≡ ( rec .₂ (1+ q) (1+ r) ε ω (s≤s q≤δ) (s≤s r≤q) d , coh-layer p δ deps-coh₂ q r ε ω q≤δ r≤q d l)
