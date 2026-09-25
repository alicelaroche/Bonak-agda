open import Prelude
open import HSet.Base
open import νSet.Context

module νSet.Frame
  (arity : ℕ)
 where

FRAME : ∀ (p δ : ℕ) → Type₁
FRAME 0 δ = ⊤
FRAME (1+ p) δ = FRAME p (1+ δ) × HSet

PAINTING : ∀ p δ
         → (frame : FRAME p δ)
         → Type₁
PAINTING 0 δ frame = ⊤
PAINTING (1+ p) δ frame = PAINTING p (1+ δ) (frame .₁) × (frame .₂ .Dom → HSet)

record DepsRestr p δ : Type₁

frame-next : ∀ p δ → DepsRestr p δ → FRAME (1+ p) δ

restr-FRAME : ∀ p δ
            → (frame : FRAME p δ)
            → (painting : PAINTING p δ frame)
            → Type₁

record DepsRestr p δ where
  eta-equality
  constructor mkDeps
  field
   frame : FRAME p δ
   painting : PAINTING p δ frame
   restr-frame : restr-FRAME p δ frame painting
open DepsRestr public

restr-FRAME zero δ frame' painting' = ⊤
restr-FRAME (1+ p) δ frame' painting' =
  Σ[ restr-frame ∈ restr-FRAME p (1+ δ) (frame' .₁) (painting' .₁) ]
  ∀ q → q ≤ δ → (ε : Fin arity)
  → frame-next p (1+ δ) (mkDeps (frame' .₁) (painting' .₁) restr-frame) .₂ .Dom
  → frame' .₂ .Dom

instance
  depsContextFst : ContextFst DepsRestr
  depsContextFst .fst deps = mkDeps (deps .frame .₁) (deps .painting .₁) (deps .restr-frame .₁)

layer : ∀ p δ → (deps : DepsRestr (1+ p) δ)
      → (d : frame-next p (1+ δ) (fst deps) .₂ .Dom)
      → HSet
layer p δ deps d = HIVec arity λ ε → deps .painting .₂ (deps .restr-frame .₂ 0 0≤n ε d)

frame-next zero δ deps = tt , HUnit
frame-next (1+ p) δ deps =
 let rec = frame-next p (1+ δ) (fst deps) in
 rec , (HΣ[ d ∈ rec .₂ ] layer p δ deps d) 
