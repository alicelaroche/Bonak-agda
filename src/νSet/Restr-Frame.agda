open import Prelude
open import HSet.Base
open import νSet.Context

module νSet.Restr-Frame
  (arity : ℕ)
 where

open import νSet.Frame arity
open import νSet.Painting arity

record DepsCoh p δ : Type₁

coh-FRAME : ∀ p δ
          → (deps : DepsRestr p δ) (ext : full deps)
          → (restr-painting : restr-PAINTING p δ deps ext)
          → Type₁

record DepsCoh p δ where
 eta-equality
 constructor mkCohDeps
 field
  deps : DepsRestr p δ
  ext : full deps
  restr-painting : restr-PAINTING p δ deps ext
  coh-frame : coh-FRAME p δ deps ext restr-painting
open DepsCoh public

restr-frame-next : ∀ p δ
                 → (coh-deps : DepsCoh p δ)
                 → restr-FRAME (1+ p) δ
                     (frame-next p δ (coh-deps .deps))
                     (painting-next p δ (coh-deps .deps) (coh-deps .ext))

deps-next : ∀ {p δ} → DepsCoh p δ → DepsRestr (1+ p) δ
deps-next coh-deps .frame = frame-next _ _ (coh-deps .deps)
deps-next coh-deps .painting = painting-next _ _ _ (coh-deps .ext)
deps-next {p} {δ} coh-deps .restr-frame = restr-frame-next p δ coh-deps

coh-FRAME zero δ deps ext restr-painting = ⊤
coh-FRAME (1+ p) δ deps ext restr-painting =
 Σ[ coh-frame ∈ coh-FRAME p (1+ δ) (fst deps) (full-fst ext) (restr-painting .₁) ]
 let deps-coh = mkCohDeps _ _ (restr-painting .₁) coh-frame in
 ∀ q r ε ω (q≤δ : q ≤ δ) (r≤q : r ≤ q)
 → (d : frame-next p (2+ δ) (fst (deps-next deps-coh)) .₂ .Dom)
 → deps .restr-frame .₂ q q≤δ ε
     (restr-frame-next p (1+ δ) deps-coh .₂
        r (↑ (r≤q ↕ q≤δ)) ω d)
 ≡ deps .restr-frame .₂ r (r≤q ↕ q≤δ) ω
     (restr-frame-next p (1+ δ) deps-coh .₂
        (1+ q) (s≤s q≤δ) ε d)

instance
  depsCohContextFst : ContextFst DepsCoh
  depsCohContextFst .fst deps-coh =
    mkCohDeps (fst (deps-coh .deps)) (full-fst (deps-coh .ext))
              (deps-coh .restr-painting .₁)
              (deps-coh .coh-frame .₁)

restr-layer : ∀ p δ (coh-deps : DepsCoh (1+ p) δ)
            → ∀ q → (q≤δ : q ≤ δ) (ε : Fin arity)
            → (d : frame-next p (2+ δ) (fst (deps-next (fst coh-deps))) .₂ .Dom)
            → layer p (1+ δ) (deps-next (fst coh-deps)) d .Dom
            → layer p δ (coh-deps .deps) (restr-frame-next p (1+ δ) (fst coh-deps) .₂ (1+ q) (s≤s q≤δ) ε d) .Dom
restr-layer p δ coh-deps q q≤δ ε d l =
  map l (λ ω l → 
  subst (λ - → coh-deps .deps .painting .₂ - .Dom)
    (coh-deps .coh-frame .₂ q 0 ε ω q≤δ 0≤n d)
    (coh-deps .restr-painting .₂ q q≤δ ε _ l))

restr-frame-next zero δ deps-coh = tt , λ _ _ _ _ → tt
restr-frame-next (1+ p) δ coh-deps =
 restr-frame-next p (1+ δ) (fst coh-deps) , λ q q≤δ ε (d , l) →
 restr-frame-next p (1+ δ) (fst coh-deps) .₂ (1+ q) (s≤s q≤δ) ε d ,
  restr-layer p δ coh-deps q q≤δ ε d l
