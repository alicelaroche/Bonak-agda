open import Prelude

module νSet.Context where

record ContextFst {ℓ} (Ctx : (p δ : ℕ) → Type ℓ) : Type ℓ where
 field
  fst : ∀ {p δ} → Ctx (1+ p) δ → Ctx p (1+ δ)
open ContextFst ⦃...⦄ public


record Context {ℓ ℓ'} (Ctx : (p δ : ℕ) → Type ℓ) (Ext : ∀ {p δ} → Ctx p (1+ δ) → Type ℓ') ⦃ _ : ContextFst Ctx ⦄ : Type (lsuc (ℓ' ⊔ ℓ)) where
 field
  snd : ∀ {p δ} → (ctx : Ctx (1+ p) δ) → Ext (fst ctx)
  mk : ∀ {p δ} → (ctx : Ctx p (1+ δ)) → Ext ctx → Ctx (1+ p) δ

  eta-mk : ∀ {p δ} → (ctx : Ctx (1+ p) δ)
         → ctx ≡ mk (fst ctx) (snd ctx)

  full-base : ∀ {p} → Ctx p 0 → Type ℓ'

 full : ∀ {p δ} → Ctx p δ → Type ℓ'
 full {p} {zero} ctx = full-base ctx
 full {p} {1+ δ} ctx = Σ[ ext ∈ Ext ctx ] full (mk ctx ext)

 full-fst : ∀ {p δ} {ctx : Ctx (1+ p) δ} → (fullCtx : full ctx) → full (fst ctx)
 full-fst {ctx = ctx} fullCtx = snd ctx , subst full (eta-mk ctx) fullCtx
 
open Context ⦃...⦄ public

