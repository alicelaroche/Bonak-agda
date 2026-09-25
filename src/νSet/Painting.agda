open import Prelude
open import HSet.Base
open import νSet.Context

module νSet.Painting
  (arity : ℕ)
 where

open import νSet.Frame arity

record DepsRestrExt {p δ} (deps : DepsRestr p (1+ δ)) : Type₁ where
 eta-equality
 constructor mkRestrExt
 field
  frame' : HSet
  painting' : frame' .Dom → HSet
  restr-frame' : (δ' : ℕ) → δ' ≤ δ → Fin arity → frame-next p (1+ δ) deps .₂ .Dom → frame' .Dom
open DepsRestrExt public

instance
  depsContext : Context DepsRestr DepsRestrExt 
  depsContext .snd deps = mkRestrExt (deps .frame .₂) (deps .painting .₂) (deps .restr-frame .₂)
  depsContext .mk deps ext = mkDeps (deps .frame , ext .frame') (deps .painting , ext .painting') (deps .restr-frame , ext .restr-frame')
  depsContext .eta-mk deps = refl
  depsContext .full-base deps = frame-next _ 0 deps .₂ .Dom → HSet

painting-at : ∀ p δ
            → (deps : DepsRestr p δ) (ext : full deps)  
            → frame-next p δ deps .₂ .Dom → HSet
painting-at p zero   deps ext d = ext d
painting-at p (1+ δ) deps ext d =
  HΣ[ l ∈ layer p δ (mk deps (ext .₁)) d ]
  painting-at (1+ p) δ (mk deps (ext .₁)) (ext .₂) (d , l)

painting-next' : ∀ p δ
              → (deps : DepsRestr p δ) (ext : full deps)
              → PAINTING p (1+ δ) (frame-next p δ deps .₁)
painting-next' zero δ deps ext = tt
painting-next' (1+ p) δ deps ext =
  painting-next' p (1+ δ) (fst deps) (full-fst ext) ,
  painting-at p (1+ δ) (fst deps) (full-fst ext)

painting-next : ∀ p δ
              → (deps : DepsRestr p δ) (ext : full deps)
              → PAINTING (1+ p) δ (frame-next p δ deps)
painting-next p δ deps ext = painting-next' p δ deps ext , painting-at p δ deps ext

restr-PAINTING-at : ∀ p δ
                  → (deps : DepsRestr (1+ p) δ) (ext : full deps)
                  → Type
restr-PAINTING-at p δ deps ext =
  ∀ q (q≤δ : q ≤ δ) (ε : Fin arity)
  → (d : frame-next p (1+ δ) (fst deps) .₂ .Dom)
  → (l : painting-next p (1+ δ) (fst deps) (full-fst ext) .₂ d .Dom)
  → deps .painting .₂ (deps .restr-frame .₂ q q≤δ ε d) .Dom

restr-PAINTING : ∀ p δ
               → (deps : DepsRestr p δ) (ext : full deps)
               → Type
restr-PAINTING zero δ deps ext   = ⊤
restr-PAINTING (1+ p) δ deps ext =
  restr-PAINTING p (1+ δ) (fst deps) (full-fst ext) ×
  restr-PAINTING-at p δ deps ext
