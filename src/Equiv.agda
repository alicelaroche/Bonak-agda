open import Prelude

module Equiv where

_∼_ : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
    → (f g : (x : A) → B x) → Type (ℓ ⊔ ℓ')
f ∼ g = (x : _) → f x ≡ g x
infixr 4 _∼_

hasLInv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Type (ℓ ⊔ ℓ')
hasLInv {A = A} {B} f = Σ[ g ∈ (B → A) ] (∀ a → g (f a) ≡ a)

hasRInv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Type (ℓ ⊔ ℓ')
hasRInv {A = A} {B} f = Σ[ g ∈ (B → A) ] (∀ b → f (g b) ≡ b)

hasQInv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Type (ℓ ⊔ ℓ')
hasQInv {A = A} {B} f = Σ[ g ∈ (B → A) ] ((∀ a → g (f a) ≡ a) × (∀ b → f (g b) ≡ b))

isEquiv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (A → B) → Type (ℓ ⊔ ℓ')
isEquiv {A = A} {B} f = hasLInv f × hasRInv f

LInv∼RInv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (f : A → B)
          → (linv : hasLInv f) (rinv : hasRInv f)
          → ∀ b → linv .₁ b ≡ rinv .₁ b
LInv∼RInv f (g , linv) (h , rinv) b =
  g b ≡⟨ cong g (rinv b) ⟩⁻¹
  g (f (h b)) ≡⟨ linv (h b) ⟩
  h b ∎

isEquiv→hasQInv : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} → (f : A → B)
                → isEquiv f → hasQInv f
isEquiv→hasQInv f ((g , linv) , (h , rinv)) =
  g , linv , λ b → trans (cong f (LInv∼RInv f (g , linv) (h , rinv) b)) (rinv b)

_≃_ : ∀ {ℓ ℓ'} (A : Set ℓ) (B : Set ℓ') → Type (ℓ ⊔ ℓ')
_≃_ A B = Σ[ f ∈ (A → B) ] isEquiv f

_∙≃_ : ∀ {ℓ ℓ' ℓ''} {A : Set ℓ} {B : Set ℓ'} {C : Set ℓ''}
     → A ≃ B → B ≃ C → A ≃ C
_∙≃_ (f  , (g  , linv)  , (h  , rinv))
     (f' , (g' , linv') , (h' , rinv')) =
     (λ a → f' (f a)) ,
     ((λ c → g (g' c)) , λ a → cong g  (linv' (f a)) ∙ linv a ) ,
     ((λ c → h (h' c)) , λ c → cong f' (rinv (h' c)) ∙ rinv' c)

module _ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (e : A ≃ B) where
  equivFun : A → B
  equivFun = e .₁

  invEq : B → A
  invEq = e .₂ .₁ .₁

  retEq : ∀ a → invEq (equivFun a) ≡ a
  retEq = isEquiv→hasQInv equivFun (e .₂) .₂ .₁

  secEq : ∀ b → equivFun (invEq b) ≡ b
  secEq = isEquiv→hasQInv equivFun (e .₂) .₂ .₂

≃id : ∀ {ℓ} (A : Set ℓ) → A ≃ A
≃id A = id , ((id , λ _ → refl) , id , (λ _ → refl))

≃sym : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → A ≃ B → B ≃ A
≃sym {A = A} {B} e = f , (g , f∘g∼id) , (g , g∘f∼id)
 where
 f = invEq e
 g = equivFun e
 f∘g∼id = secEq e
 g∘f∼id = retEq e

≃sym-id : ∀ {ℓ} (A : Set ℓ) → ≃sym (≃id A) ≡ ≃id A
≃sym-id A = refl

eq→isEquiv : ∀ {ℓ} {A B : Set ℓ} → A ≡ B → A ≃ B
eq→isEquiv eq = (transport eq)
              , (transport (sym eq) , subst-sym-l eq)
              , (transport (sym eq) , subst-sym-r eq)

isHAE : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → Type (ℓ ⊔ ℓ')
isHAE {A = A} {B} f = Σ[ g ∈ (B → A) ]
                      Σ[ η ∈ (∀ a → g (f a) ≡ a) ]
                      Σ[ ε ∈ (∀ b → f (g b) ≡ b) ]
                      ((x : A) → cong f (η x) ≡ ε (f x))

∼natural : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f g : A → B} (α : ∀ a → f a ≡ g a)
         → {x y : A} (p : x ≡ y) → (α x) ∙ (cong g p) ≡ (cong f p) ∙ (α y)
∼natural α refl = trans-identity-r (α _)

∼natural' : ∀ {ℓ} {A : Type ℓ} {f : A → A} (α : ∀ a → f a ≡ a) (x : A)
          → α (f x) ≡ cong f (α x)
∼natural' {f = f} α x =
 α (f x) ≡⟨ trans-identity-r _ ⟩⁻¹
 α (f x) ∙ refl ≡⟨ cong (α (f x) ∙_) (trans-sym-r (cong id (α x))) ⟩⁻¹
 α (f x) ∙ (cong id (α x) ∙ sym (cong id (α x))) ≡⟨ trans-assoc (α (f x)) _ _ ⟩⁻¹
 (α (f x) ∙ cong id (α x)) ∙ sym (cong id (α x))  ≡⟨ cong (_∙ sym (cong id (α x))) (∼natural α (α x)) ⟩
 (cong f (α x) ∙ (α x)) ∙ sym (cong id (α x)) ≡⟨ cong (λ - → (cong f (α x) ∙ (α x)) ∙ sym -) (cong-id (α x)) ⟩
 (cong f (α x) ∙ (α x)) ∙ sym (α x) ≡⟨ trans-assoc (cong f (α x)) _ _ ⟩
 cong f (α x) ∙ ((α x) ∙ sym (α x)) ≡⟨ cong (cong f (α x) ∙_) (trans-sym-r (α x)) ⟩
 cong f (α x) ∙ refl ≡⟨ trans-identity-r (cong f (α x)) ⟩
 cong f (α x) ∎

hasQInv→isHAE : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (f : A → B) → hasQInv f → isHAE f
hasQInv→isHAE f (g , linv , rinv) =
 g , (linv , (λ b → sym (rinv (f (g b))) ∙ cong f (linv (g b)) ∙ rinv b) , helper)
 where
   helper : ∀ a
          → cong f (linv a)
          ≡ sym (rinv (f (g (f a)))) ∙ cong f (linv (g (f a))) ∙ rinv (f a)
   helper a =
     cong f (linv a)
       ≡⟨ cong-id (cong f (linv a)) ⟩⁻¹
     cong id (cong f (linv a))
       ≡⟨ cong (_∙ cong id (cong f (linv a))) (trans-sym-l (rinv (id (f (g (f a)))))) ⟩⁻¹
     (sym (rinv (f (g (f a)))) ∙ rinv (f (g (f a)))) ∙ cong id (cong f (linv a)) 
       ≡⟨ trans-assoc (sym (rinv (f (g (f a))))) _ _ ⟩
     sym (rinv (f (g (f a)))) ∙ rinv (f (g (f a))) ∙ cong id (cong f (linv a)) 
       ≡⟨ cong (sym (rinv (f (g (f a)))) ∙_) (∼natural rinv (cong f (linv a))) ⟩
     sym (rinv (f (g (f a)))) ∙ cong (λ - → f (g -)) (cong f (linv a)) ∙ rinv (f a)
       ≡⟨ cong (λ - → sym (rinv (f (g (f a)))) ∙ - ∙ rinv (f a)) (cong-∘ f (λ - → f (g -)) _) ⟩ 
     sym (rinv (f (g (f a)))) ∙ cong (λ - → f (g (f -))) (linv a) ∙ rinv (f a)
       ≡⟨ cong (λ - → sym (rinv (f (g (f a)))) ∙ - ∙ rinv (f a)) (cong-∘ (λ - → g (f -)) f _) ⟩⁻¹
     sym (rinv (f (g (f a)))) ∙ cong f (cong (λ - → g (f -)) (linv a)) ∙ rinv (f a) 
       ≡⟨ cong (λ - → sym (rinv (f (g (f a)))) ∙ cong f - ∙ rinv (f a)) (∼natural' linv a) ⟩⁻¹
     sym (rinv (f (g (f a)))) ∙ cong f (linv (g (f a))) ∙ rinv (f a) ∎

Σ-≃-fst : ∀ {a₁ a₂ b}
        → {A : Set a₁} {A' : Set a₂} {B : A' → Set b}
        → (A≈ : A ≃ A')
        → Σ A (λ - → B (equivFun A≈ -)) ≃ Σ A' B
Σ-≃-fst {A = A} {A'} {B} A≈ = f , (g , f-linv) , (g , f-rinv)
 where
 hae : isHAE (equivFun A≈)
 hae = hasQInv→isHAE (equivFun A≈) ((invEq A≈) , ((retEq A≈) , (secEq A≈)))

 η = hae .₂ .₁
 ε = hae .₂ .₂ .₁
 γ = hae .₂ .₂ .₂

 f : Σ A (λ - → B (equivFun A≈ -)) → Σ A' B
 f (a , b) = (equivFun A≈ a) , b

 g : Σ A' B → Σ A (λ - → B (equivFun A≈ -))
 g (a , b) = (invEq A≈ a) , subst B (sym (ε a)) b

 f-linv-helper : ∀ a b → subst (λ - → B (equivFun A≈ -)) (η a)
                        (subst B (sym (ε (equivFun A≈ a))) b)
                       ≡ b 
 f-linv-helper a b =
  subst (λ - → B (equivFun A≈ -)) (η a) (subst B (sym (ε (equivFun A≈ a))) b)
    ≡⟨ subst-∘ (η a)  _ ⟩
  subst B (cong (equivFun A≈) (η a)) (subst B (sym (ε (equivFun A≈ a))) b)
    ≡⟨ cong (λ - → subst B - (subst B (sym (ε (equivFun A≈ a))) b)) (γ a) ⟩
  subst B (ε (equivFun A≈ a)) (subst B (sym (ε (equivFun A≈ a))) b)
    ≡⟨ subst-sym-r (ε (equivFun A≈ a)) b ⟩
  b ∎

 f-linv : (ab : Σ A (λ - → B (equivFun A≈ -))) → g (f ab) ≡ ab
 f-linv (a , b) = Σ-≡→≡ (η a , f-linv-helper a b)
 
 f-rinv : (ab : Σ A' B) → f (g ab) ≡ ab
 f-rinv (a , b) = Σ-≡→≡ (ε a , subst-sym-r (ε a) b)

Σ-≃-snd : ∀ {a b₁ b₂}
        → {A : Set a} {B : A → Set b₁} {B' : A → Set b₂}
        → (B≃ : ∀ a → B a ≃ B' a)
        → Σ A B ≃ Σ A B'
Σ-≃-snd {A = A} {B} {B'} B≈ = f , (g , f-linv) , (g , f-rinv)
 where
 f : Σ A B → Σ A B'
 f (a , b) = a , equivFun (B≈ a) b

 g : Σ A B' → Σ A B
 g (a , b) = a , invEq (B≈ a) b

 f-linv : (ab : Σ A B) → g (f ab) ≡ ab
 f-linv (a , b) = Σ-≡→≡ (refl , retEq (B≈ a) b)

 f-rinv : (ab : Σ A B') → f (g ab) ≡ ab
 f-rinv (a , b) = Σ-≡→≡ (refl , secEq (B≈ a) b)
 
Σ-≃ : ∀ {a₁ a₂ b₁ b₂}
    → {A : Set a₁} {A' : Set a₂}
    → {B : A → Set b₁} {B' : A' → Set b₂}
    → (A≃ : A ≃ A')
    → (B≃ : ∀ a → B a ≃ B' (equivFun A≃ a))
    → Σ A B ≃ Σ A' B'
Σ-≃ A≃ B≃ = Σ-≃-snd B≃ ∙≃ Σ-≃-fst A≃

Σ-≃-eq : ∀ {a₁ a₂ b₁ b₂}
    → {A : Set a₁} {A' : Set a₂}
    → {B : A → Set b₁} {B' : A' → Set b₂}
    → (A≃ : A ≃ A')
    → (B≃ : ∀ a → B a ≃ B' (equivFun A≃ a))
    → (ab : Σ A B)
    → Σ-≃ {B' = B'} A≃ B≃ .₁ ab ≡ ((A≃ .₁ (ab .₁)) , (B≃ (ab .₁) .₁ (ab .₂)))
Σ-≃-eq A≃ B≃ ab = refl

module ≃Π
  (fe : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
      → (f g : (a : A) → B a)
      → (∀ a → f a ≡ g a)
      → f ≡ g)
  where

  Π-≃-fst : ∀ {ℓ ℓ' ℓ''} {A : Type ℓ} {A' : Type ℓ'} {B : A' → Type ℓ''}
          → (A≃ : A ≃ A')
          → ((a : A) → B (equivFun A≃ a)) ≃ ((a : A') → B a)
  Π-≃-fst {A = A} {A'} {B} A≃ = f , (g , f-linv) , (g , f-rinv)
    where
    hae : isHAE (equivFun A≃)
    hae = hasQInv→isHAE (equivFun A≃) ((invEq A≃) , ((retEq A≃) , (secEq A≃)))

    η = hae .₂ .₁
    ε = hae .₂ .₂ .₁
    γ = hae .₂ .₂ .₂

    f : ((a : A) → B (equivFun A≃ a)) → (a : A') → B a
    f h a = subst B (ε a) (h (invEq A≃ a))

    g : ((a : A') → B a) → (a : A) → B (equivFun A≃ a)
    g h a = h (equivFun A≃ a)

    f-linv : (h : (a : A) → B (equivFun A≃ a)) → g (f h) ≡ h
    f-linv h = fe _ _ helper
     where
     helper : ∀ a
            → subst B (ε (equivFun A≃ a)) (h (invEq A≃ (equivFun A≃ a)))
            ≡ h a
     helper a =
       subst B (ε (equivFun A≃ a)) (h (invEq A≃ (equivFun A≃ a)))
         ≡⟨ cong (λ - → subst B - (h (invEq A≃ (equivFun A≃ a)))) (γ a) ⟩⁻¹
       subst B (cong (equivFun A≃) (η a)) (h (invEq A≃ (equivFun A≃ a)))
         ≡⟨ subst-∘ (η a) _ ⟩⁻¹
       subst (λ - → B (equivFun A≃ -)) (η a) (h (invEq A≃ (equivFun A≃ a)))
         ≡⟨ dcong h (η a) ⟩ 
       h a ∎

    f-rinv : (h : (a : A') → B a) → f (g h) ≡ h
    f-rinv h = fe _ _ λ a → dcong h (ε a)
    
  Π-≃-snd : ∀ {a b₁ b₂}
          → {A : Set a} {B : A → Set b₁} {B' : A → Set b₂}
          → (B≃ : ∀ a → B a ≃ B' a)
          → ((a : A) → B a) ≃ ((a : A) → B' a)
  Π-≃-snd {A = A} {B} {B'} B≈ = f , ((g , f-linv) , (g , f-rinv))
    where
    f : ((a : A) → B a) → ((a : A) → B' a)
    f f' a = equivFun (B≈ a) (f' a)

    g : ((a : A) → B' a) → ((a : A) → B a)
    g g' a = invEq (B≈ a) (g' a)

    f-linv : (f' : (a : A) → B a) → g (f f') ≡ f'
    f-linv f' = fe _ _ λ a → retEq (B≈ a) (f' a)

    f-rinv : (g' : (a : A) → B' a) → f (g g') ≡ g'
    f-rinv g' = fe _ _ λ a → secEq (B≈ a) (g' a)

  Π-≃ : ∀ {a₁ a₂ b₁ b₂}
      → {A : Set a₁} {A' : Set a₂}
      → {B : A → Set b₁} {B' : A' → Set b₂}
      → (A≃ : A ≃ A')
      → (B≃ : ∀ a → B a ≃ B' (equivFun A≃ a))
      → ((a : A) → B a) ≃ ((a : A') → B' a)
  Π-≃ A≃ B≃ = Π-≃-snd B≃ ∙≃ Π-≃-fst A≃

{-

-}
