open import Prelude
open import HSet.Base
open import νSet.Context

module νSet.Coh-Painting
  (arity : ℕ)
 where

open import νSet.Frame arity
open import νSet.Painting arity
open import νSet.Restr-Frame arity
open import νSet.Restr-Painting arity
open import νSet.Coh-Frame arity

record DepsCoh₂Ext {p δ : ℕ} (deps-coh₂ : DepsCoh₂ p (1+ δ)) : Type₁ where
 eta-equality
 constructor mkDepsCoh₂Ext
 field
  coh-painting' :  ∀ q r (ε ω : Fin arity) (q≤δ : q ≤ δ) (r≤q : r ≤ q)
                → (d : frame-next p (2+ δ) (fst (deps-next (deps-coh₂ .deps-coh))) .₂ .Dom)
                → (l : painting-next p (2+ δ)
                         (fst (deps-next (deps-coh₂ .deps-coh)))
                         (full-fst (depsFull-next (deps-coh₂ .deps-coh) (deps-coh₂ .ext-coh))) .₂ d .Dom)
                → subst (λ - → deps-coh₂ .deps-coh .ext .₁ .painting' - .Dom)
                    (deps-coh₂ .ext-coh .₁ .coh-frame' q r ε ω q≤δ r≤q d)
                    (deps-coh₂ .ext-coh .₁ .restr-painting' q q≤δ ε _
                      (restr-painting-next p (1+ δ) _ (deps-coh₂ .ext-coh) .₂ r (↑ (r≤q ↕ q≤δ)) ω d l))
                ≡ deps-coh₂ .ext-coh .₁ .restr-painting' r (r≤q ↕ q≤δ) ω _
                     (restr-painting-next p (1+ δ) _ (deps-coh₂ .ext-coh) .₂ (1+ q) (s≤s q≤δ) ε d l)
open DepsCoh₂Ext

instance
  depsCoh₂Context : Context DepsCoh₂ DepsCoh₂Ext
  depsCoh₂Context .snd ctx = mkDepsCoh₂Ext (ctx .coh-painting .₂)
  depsCoh₂Context .mk ctx ext = mkCoh₂Deps (mk (ctx .deps-coh) (ctx .ext-coh .₁)) (ctx .ext-coh .₂) (ctx .coh-painting , ext .coh-painting')
  depsCoh₂Context .eta-mk ctx = refl
  depsCoh₂Context .full-base {p = p} ctx = frame-next (2+ p) 0 (deps-next (deps-coh-next ctx)) .₂ .Dom → HSet

depsCohFull-next : ∀ {p δ} → (deps-coh₂ : DepsCoh₂ p δ) → full deps-coh₂ → full (deps-coh-next deps-coh₂)
depsCohFull-next {p} {zero} deps-coh₂ ext-coh₂ = ext-coh₂
depsCohFull-next {p} {1+ δ} deps-coh₂ ext-coh₂ =
  _ , depsCohFull-next (mk deps-coh₂ (ext-coh₂ .₁)) (ext-coh₂ .₂) 


postulate
  coh-painting-at : ∀ p δ
                  → (deps-coh₂ : DepsCoh₂ p δ) (ext-coh₂ : full deps-coh₂)
                  → coh-PAINTING-at p δ (deps-coh-next deps-coh₂) (depsCohFull-next deps-coh₂ ext-coh₂)

{-
coh-painting-at p δ deps-coh₂ ext-coh₂ q zero ε ω q≤δ 0≤n d (l , c) =
  sym (map-‼ ω l λ θ l →
    subst (λ - → painting-next p δ _ _ .₂ - .Dom)
      (coh-frame-next p δ _ .₂ q 0 ε θ q≤δ 0≤n _)
      (restr-painting-next p δ _ _ .₂ q q≤δ ε _ l))
coh-painting-at p (1+ δ) deps-coh₂ ext-coh₂ (1+ q) (1+ r) ε ω (s≤s q≤δ) (s≤s r≤q) d l =
  {!!}
-}

coh-painting-next' : ∀ p δ
                   → (deps-coh₂ : DepsCoh₂ p δ) (ext-coh₂ : full deps-coh₂)
                   → coh-PAINTING p (1+ δ) (fst (deps-coh-next deps-coh₂)) (full-fst (depsCohFull-next deps-coh₂ ext-coh₂))
coh-painting-next' zero δ deps-coh₂ ext-coh₂ = tt
coh-painting-next' (1+ p) δ deps-coh₂ ext-coh₂ =
  coh-painting-next' p (1+ δ) (fst deps-coh₂) (full-fst ext-coh₂) ,
  coh-painting-at p (1+ δ) (fst deps-coh₂) (full-fst ext-coh₂)
