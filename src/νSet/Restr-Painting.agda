open import Prelude
open import HSet.Base
open import νSet.Context

module νSet.Restr-Painting
  (arity : ℕ)
 where

open import νSet.Frame arity
open import νSet.Painting arity
open import νSet.Restr-Frame arity

record DepsCohExt {p δ : ℕ} (deps-coh : DepsCoh p (1+ δ)) : Type₁ where
 eta-equality
 constructor mkCohExt
 field
   restr-painting' : ∀ q → (q≤δ : q ≤ δ) (ε : Fin arity)
                   → (d : frame-next p (1 + δ) (deps-coh .deps) .₂ .Dom)
                   → (l : painting-next p (1+ δ) (deps-coh .deps) (deps-coh .ext) .₂ d .Dom)
                   → deps-coh .ext .₁ .painting'
                       (deps-coh .ext .₁ .restr-frame' q q≤δ ε d) .Dom
   coh-frame' : ∀ q r (ε ω : Fin arity) (q≤δ : q ≤ δ) (r≤q : r ≤ q)
             → (d : frame-next p (2+ δ) (fst (deps-next deps-coh)) .₂ .Dom)
             → deps-coh .ext .₁ .restr-frame' q q≤δ ε
                 (restr-frame-next p (1+ δ) deps-coh .₂ r (↑ (r≤q ↕ q≤δ)) ω d)
             ≡ deps-coh .ext .₁ .restr-frame' r (r≤q ↕ q≤δ) ω
                 (restr-frame-next p (1+ δ) deps-coh .₂ (1+ q) (s≤s q≤δ) ε d)
open DepsCohExt public

instance
  depsCohContext : Context DepsCoh DepsCohExt
  depsCohContext .snd deps = mkCohExt (deps .restr-painting .₂) (deps .coh-frame .₂)
  depsCohContext .mk deps-coh ext-coh =
    mkCohDeps (mk (deps-coh .deps) (deps-coh .ext .₁)) (deps-coh .ext .₂)
              (deps-coh .restr-painting , ext-coh .restr-painting')
              (deps-coh .coh-frame , ext-coh .coh-frame')
  depsCohContext .eta-mk deps = refl
  depsCohContext .full-base {p} deps-coh = frame-next (1+ p) 0 (deps-next deps-coh) .₂ .Dom → HSet

depsFull-next : ∀ {p δ} → (deps-coh : DepsCoh p δ) → full deps-coh → full (deps-next deps-coh)
depsFull-next {p} {zero} deps-coh ext-coh = ext-coh
depsFull-next {p} {1+ δ} deps-coh ext-coh =
  _ , depsFull-next (mk deps-coh (ext-coh .₁)) (ext-coh .₂) 

restr-painting-at : ∀ p δ (deps-coh : DepsCoh p δ) (ext-coh : full deps-coh)
                  → restr-PAINTING-at p δ (deps-next deps-coh) (depsFull-next deps-coh ext-coh)
restr-painting-at p δ deps-coh ext-coh zero 0≤n ε d (l , c) = l ‼ ε
restr-painting-at p (1+ δ) deps-coh ext-coh (1+ q) (s≤s q≤δ) ε d (l , c) =
  (restr-layer p δ (mk deps-coh (ext-coh .₁)) q  q≤δ ε d l) ,
  restr-painting-at (1+ p) δ (mk deps-coh (ext-coh .₁)) (ext-coh .₂) q q≤δ ε (d , l) c

restr-painting-next' : ∀ p δ
                     → (deps-coh : DepsCoh p δ) (ext-coh : full deps-coh)
                     → restr-PAINTING p (1+ δ) (fst (deps-next deps-coh)) (full-fst (depsFull-next deps-coh ext-coh))
restr-painting-next' 0 δ deps-coh ext-coh = tt
restr-painting-next' (1+ p) δ deps-coh ext-coh =
  restr-painting-next' p (1+ δ) (fst deps-coh) (full-fst ext-coh) ,
  restr-painting-at p (1+ δ) (fst deps-coh) (full-fst ext-coh)

restr-painting-next : ∀ p δ
                    → (deps-coh : DepsCoh p δ) (ext-coh : full deps-coh)
                    → restr-PAINTING (1+ p) δ (deps-next deps-coh) (depsFull-next deps-coh ext-coh)
restr-painting-next p δ deps-coh ext-coh =
  restr-painting-next' p δ deps-coh ext-coh ,
  restr-painting-at p δ deps-coh ext-coh 

coh-PAINTING-at : ∀ p δ
                → (deps-coh : DepsCoh (1+ p) δ) (ext-coh : full deps-coh)
                → Type
coh-PAINTING-at p δ deps-coh ext-coh =
  ∀ q r (ε ω : Fin arity) (q≤δ : q ≤ δ) (r≤q : r ≤ q)
  → (d : frame-next p (2+ δ) (fst (fst (deps-next deps-coh))) .₂ .Dom)
  → (l : painting-next p (2+ δ) _ (full-fst (full-fst ((depsFull-next deps-coh ext-coh)))) .₂ d .Dom)
  → subst (λ - → deps-coh .deps .painting .₂ - .Dom)
      (deps-coh .coh-frame .₂ q r ε ω q≤δ r≤q d)
      (deps-coh .restr-painting .₂ q q≤δ ε _
        (restr-painting-next p (1+ δ) (fst deps-coh) (full-fst ext-coh) .₂ r (↑ (r≤q ↕ q≤δ)) ω d l))
  ≡ deps-coh .restr-painting .₂ r (r≤q ↕ q≤δ) ω _
      (restr-painting-next p (1+ δ) (fst deps-coh) (full-fst ext-coh) .₂ (1+ q) (s≤s q≤δ) ε d l)

coh-PAINTING : ∀ p δ 
             → (deps-coh : DepsCoh p δ) (ext-coh : full deps-coh)
             → Type
coh-PAINTING zero δ deps-coh ext-coh = ⊤
coh-PAINTING (1+ p) δ deps-coh ext-coh =
  coh-PAINTING p (1+ δ) (fst deps-coh) (full-fst ext-coh) ×
  coh-PAINTING-at p δ deps-coh ext-coh
