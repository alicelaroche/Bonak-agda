open import Prelude

module Presheaf.Zipper (arity : Type) where

open import Presheaf.Base arity

open import Inequalities
open import HSet

F0-< : (m : ℕ) → Type₁
F0-< zero   = ⊤
F0-< (1+ m) = F0-< m × HSet

Face-< : (m : ℕ) → F0-< (1+ m) → Type₁
Face-< zero   F0s = ⊤
Face-< (1+ m) ((F0s , F0) , F0')  =
  Face-< m (F0s , F0) × (∀ p {δ} → [ p ≤ m ][ δ ]₂ → arity → F0' .Dom → F0 .Dom)

Coh-< : (m : ℕ) → (F0s : F0-< (2+ m)) → Face-< (1+ m) F0s → Type₁
Coh-< zero F0s faces = ⊤
Coh-< (1+ m) F0s ((faces , face) , face') =
  Coh-< m (F0s .₁) (faces , face) ×
  (∀ p q {δ} (p≤q≤m : [ p ≤ q ≤ m ][ δ ]₃) ε ω d
  → face q (drop₃-1 p≤q≤m) ε (face' p (↑₂ drop₃-2 p≤q≤m) ω d)
  ≡ face p (drop₃-2 p≤q≤m) ω (face' (1+ q) (⇑₂ drop₃-1 p≤q≤m) ε d))

record Presheaf-< (m : ℕ) : Type₁ where
 field
   F0 : F0-< (2+ m)
   Face : Face-< (1 + m) F0
   Coh : Coh-< m F0 Face
open Presheaf-< public

psh₁ : ∀ {m} → Presheaf-< (1+ m) → Presheaf-< m
psh₁ psh-< .F0 = psh-< .F0 .₁
psh₁ psh-< .Face = psh-< .Face .₁
psh₁ psh-< .Coh = psh-< .Coh .₁

record Presheaf-zipper (m : ℕ) : Type₁ where
  field
   |F0-<| : F0-< m
   |F0-≥| : ∀ n → HSet
   |Face-<| : Face-< m (|F0-<| , |F0-≥| 0)
   |Face-≥| : ∀ n p {δ}
            → [ p ≤ n + m ][ δ ]₂ → arity
            → |F0-≥| (1+ n) .Dom
            → |F0-≥| n .Dom
   |Coh-<| : Coh-< m ((|F0-<| , |F0-≥| 0) , |F0-≥| 1) (|Face-<| , |Face-≥| 0)
   |Coh-≥| : ∀ n p q {δ}
           → (p≤q≤m : [ p ≤ q ≤ n + m ][ δ ]₃)
           → (ε ω : arity)
           → (d : |F0-≥| (2+ n) .Dom)
           → |Face-≥| n q (drop₃-1 p≤q≤m) ε (|Face-≥| (1+ n) p (↑₂ drop₃-2 p≤q≤m) ω d)
           ≡ |Face-≥| n p (drop₃-2 p≤q≤m) ω (|Face-≥| (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤m) ε d)
open Presheaf-zipper public

bump-zipper : ∀ m → Presheaf-zipper m → Presheaf-zipper (1+ m)
bump-zipper m zipper .|F0-<| = zipper .|F0-<| , zipper .|F0-≥| 0
bump-zipper m zipper .|F0-≥| = zipper .|F0-≥| ∘ suc
bump-zipper m zipper .|Face-<| = zipper .|Face-<| , zipper .|Face-≥| 0
bump-zipper m zipper .|Face-≥| = zipper .|Face-≥| ∘ suc
bump-zipper m zipper .|Coh-<| = zipper .|Coh-<| , (λ p q {δ} → zipper .|Coh-≥| 0 p q)
bump-zipper m zipper .|Coh-≥| = zipper .|Coh-≥| ∘ suc

psh→zipper : Presheaf → Presheaf-zipper 0
psh→zipper psh .|F0-<| = tt
psh→zipper psh .|F0-≥| = psh .F0
psh→zipper psh .|Face-<| = tt
psh→zipper psh .|Face-≥| = psh .Face
psh→zipper psh .|Coh-<| = tt
psh→zipper psh .|Coh-≥| = psh .Face-coh

psh→psh-< : ∀ {m} → Presheaf-zipper m → Presheaf-< m
psh→psh-< psh .F0 = (psh .|F0-<| , psh .|F0-≥| zero) , psh .|F0-≥| 1
psh→psh-< psh .Face = psh .|Face-<| , psh .|Face-≥| 0
psh→psh-< psh .Coh = psh .|Coh-<|
