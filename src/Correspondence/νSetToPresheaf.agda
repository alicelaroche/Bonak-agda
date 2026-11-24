open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module Correspondence.νSetToPresheaf
  (fe-axiom : FunExt-Axiom)
  (ua-axiom : Univalence-Axiom) 
  (arity : Type)
  where

open import Inequalities

open import HSet

open import Presheaf fe-axiom ua-axiom arity
open import νSet fe-axiom ua-axiom arity

open FE fe-axiom

getFrame : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
         → (D : νSet-< n)
         → frame n q (drop₃-1 p≤q≤n) D .Dom
         → frame n p (drop₃-2 p≤q≤n) D .Dom
getFrame n p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) D d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = d
getFrame n p q {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) D d =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in 
  getFrame n (1+ p) q {δ} 1+p≤q≤n D d .₁

getPainting : ∀ n p q {δ} (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
            → (D : νSet-< n) (E : νSet-= n D)
            → (d : frame n p (drop₃-2 p≤q≤n) D .Dom)
            → (c : painting n p (drop₃-2 p≤q≤n) D E d .Dom)
            → Σ[ d ∈ frame n q (drop₃-1 p≤q≤n) D .Dom ]
              painting n q (drop₃-1 p≤q≤n) D E d .Dom
getPainting n p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) D E d c
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = d , c
getPainting n p q {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) D E d (l , c) =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  getPainting n (1+ p) q {δ} 1+p≤q≤n D E (d , l) c

getFrame-compose : ∀ n p q r {δ} → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ][ δ ]₄) 
                 → (D : νSet-< n)
                 → (d : frame n q (drop₃-1 (drop₄-1 p≤r≤q≤n)) D .Dom)
                 → getFrame n p r (drop₄-3 p≤r≤q≤n) D (
                   getFrame n r q (drop₄-1 p≤r≤q≤n) D d)
                 ≡ getFrame n p q (drop₄-2 p≤r≤q≤n) D d
getFrame-compose n p q r {zero} (ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) D d
  with recover-nat-eq p r Hpr | recover-nat-eq δrq δpq Hprq | recover-nat-eq δrn δpn Hprn
... | refl | refl | refl = refl 
getFrame-compose n p (1+ q) (1+ r) {1+ δ} (ineq₄ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) D d =
    let 1+p≤r≤q≤n = ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn  in
    cong (λ - → - .₁) (getFrame-compose n (1+ p) (1+ q) (1+ r) {δ} 1+p≤r≤q≤n D d)

getFrame-getPainting : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃) 
                     → (D : νSet-< n) (E : νSet-= n D)
                     → (d : frame n p (drop₃-2 p≤q≤n) D .Dom)
                     → (c : painting n p (drop₃-2 p≤q≤n) D E d .Dom)           
                     → getFrame n p q p≤q≤n D (getPainting n p q p≤q≤n D E d c .₁)
                     ≡ d
getFrame-getPainting n p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) D E d c
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
getFrame-getPainting n p q {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) D E d (l , c) =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  cong (λ - → - .₁) (getFrame-getPainting n (1+ p) q {δ} 1+p≤q≤n D E (d , l) c)

getFrame-getPainting' : ∀ n p q r {δ} → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ][ δ ]₄) 
                     → (D : νSet-< n) (E : νSet-= n D)
                     → (d : frame n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
                     → (c : painting n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) D E d .Dom)
                     → getFrame n r q (drop₄-1 p≤r≤q≤n) D
                         (getPainting n p q (drop₄-2 p≤r≤q≤n) D E d c .₁)
                     ≡ getPainting n p r (drop₄-3 p≤r≤q≤n) D E d c .₁
getFrame-getPainting' n p q r {zero} p≤p≤q≤n@(ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) D E d c
  with recover-nat-eq p r Hpr | recover-nat-eq δrq δpq Hprq | recover-nat-eq δrn δpn Hprn
... | refl | refl | refl = getFrame-getPainting n p q (drop₄-1 p≤p≤q≤n) D E d c
getFrame-getPainting' n p q r {1+ δ} (ineq₄ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) D E d (l , c) =
  let 1+p≤r≤q≤n = ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn  in
  getFrame-getPainting' n (1+ p) q r {δ} 1+p≤r≤q≤n D E (d , l) c

getFrameRestr : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
              → (ε : arity)
              → (D : νSet-< (1+ n))
              → (d : frame (1+ n) q (↑₂ drop₃-1 p≤q≤n) D .Dom)
              → getFrame n p q p≤q≤n (D .₁) (restr-frame n q q (◆₃ drop₃-1 p≤q≤n) ε D d)
              ≡ restr-frame n p q p≤q≤n ε D (getFrame (1+ n) p q (↑₃ p≤q≤n) D d)
getFrameRestr n p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) ε D d
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
getFrameRestr n p (1+ q) {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) ε D d =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  cong (λ - → - .₁) ( getFrameRestr n (1+ p) (1+ q) {δ} 1+p≤q≤n ε D d)

getPaintingRestr : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃) 
                 → (ε : arity)
                 → (D : νSet-< (1+ n)) (E : νSet-= (1+ n) D)
                 → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
                 → (c : painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D E d .Dom)
                 → getPainting n q n (◆₃' drop₃-1 p≤q≤n) (D .₁) (D .₂) _
                     (getPainting (1+ n) p (1+ q) (↑₃' p≤q≤n) D E d c .₁ .₂ ε)
                 ≡ getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁) (D .₂) _
                     (restr-painting n p q p≤q≤n ε D E d c)
getPaintingRestr n p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) ε D E d c
  with recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = refl
getPaintingRestr n p (1+ q) {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) ε D E d (l , c) =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  getPaintingRestr n (1+ p) (1+ q) {δ} 1+p≤q≤n ε D E (d , l) c

νFace : ∀ n p {δ} (p≤n : [ p ≤ n ][ δ ]₂) → arity
     → (D : νSet-< (1+ n))
     → (d : frame (1+ n) (1+ n) (◆₂ 1+ n) D .Dom)
     → Σ[ d ∈ frame n n (◆₂ n) (D .₁) .Dom ]
      (painting n n (◆₂ n) (D .₁) (D .₂) d .Dom)
νFace n p p≤n ε D d =
 getPainting n p n (◆₃' p≤n) (D .₁) (D .₂) _
   (getFrame (1+ n) (1+ p) (1+ n) (⇑₃ ◆₃' p≤n) D d .₂ ε)

opaque
  νFace-coh : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃) 
           → (ε ω : arity)
           → (D : νSet-< (2+ n))
           → (d : frame (2+ n) (2+ n) (◆₂ 2+ n) D .Dom)
           → νFace n q (drop₃-1 p≤q≤n) ε (D .₁)
               (νFace (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω D d .₁)
           ≡ νFace n p (drop₃-2 p≤q≤n) ω (D .₁)
               (νFace (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁)
  νFace-coh n p q p≤q≤n ε ω D d =
    νFace n q (drop₃-1 p≤q≤n) ε (D .₁)
      (νFace (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω D d .₁)
      ≡⟨ cong (λ - → getPainting n q n (◆₃' drop₃-1 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _ (- .₂ ε))
              (getFrame-getPainting' (1+ n) p (1+ n) (1+ q) (◆₄' (↑₃' p≤q≤n)) (D .₁) (D .₂) _
                 (getFrame (2+ n) (1+ p) (2+ n) (↑₃' ⇑₃ ◆₃' drop₃-2 p≤q≤n) D d .₂ ω)) ⟩
    getPainting n q n (◆₃' drop₃-1 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
      (getPainting (1+ n) p (1+ q) (↑₃' p≤q≤n) (D .₁) (D .₂) _
         (getFrame (2+ n) (1+ p) (2+ n) (↑₃' ⇑₃ ◆₃' drop₃-2 p≤q≤n) D d .₂ ω) .₁ .₂ ε)
      ≡⟨ getPaintingRestr n p q p≤q≤n ε (D .₁) (D .₂) _ _ ⟩
    getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
      (restr-painting n p q p≤q≤n ε (D .₁) (D .₂) _
         (getFrame (2+ n) (1+ p) (2+ n) (↑₃' ⇑₃ ◆₃' drop₃-2 p≤q≤n) D d .₂ ω))
      ≡⟨ cong₂ (getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂))
               (coh-frame n p q p (◆₄ p≤q≤n) ε ω D _) ⟩
    getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
      (restr-frame (1+ n) (1+ p) (1+ q) (⇑₃ p≤q≤n) ε D
         (getFrame (2+ n) (1+ p) (2+ n) (↑₃' ⇑₃ ◆₃' drop₃-2 p≤q≤n) D d) .₂ ω)
      ≡⟨ cong (λ - → getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
                  (restr-frame (1+ n) (1+ p) (1+ q) (⇑₃ p≤q≤n) ε D - .₂ ω))
              (getFrame-compose (2+ n) (1+ p) (2+ n) (1+ q) (◆₄' ↑₃ ⇑₃ p≤q≤n) D d) ⟩⁻¹
    getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
      (restr-frame (1+ n) (1+ p) (1+ q) (⇑₃ p≤q≤n) ε D
         (getFrame (2+ n) (1+ p) (1+ q) (↑₃ ⇑₃ p≤q≤n) D
            (getFrame (2+ n) (1+ q) (2+ n) (↑₃' ⇑₃ ◆₃' drop₃-1 p≤q≤n) D d)) .₂ ω)
      ≡⟨ cong (λ - → getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _ (- .₂ ω))
          (getFrameRestr (1+ n) (1+ p) (1+ q) (⇑₃ p≤q≤n) ε D _) ⟩⁻¹
    getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
      (getFrame (1+ n) (1+ p) (1+ q) (⇑₃ p≤q≤n) (D .₁)
         (restr-frame (1+ n) (1+ q) (1+ q) (⇑₃ ◆₃ drop₃-1 p≤q≤n) ε D
            (getFrame (2+ n) (1+ q) (2+ n) (↑₃' ⇑₃ ◆₃' drop₃-1 p≤q≤n) D d)) .₂ ω)
      ≡⟨ cong (λ - → getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
                       (getFrame (1+ n) (1+ p) (1+ q) (⇑₃ p≤q≤n) (D .₁) - .₂ ω))
              (getFrame-getPainting (1+ n) (1+ q) (1+ n) (⇑₃ ◆₃' drop₃-1 p≤q≤n) (D .₁) (D .₂) _
                 (getFrame (2+ n) (2+ q) (2+ n) (⇑₃ ⇑₃ ◆₃' drop₃-1 p≤q≤n) D d .₂ ε)) ⟩⁻¹
    getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _
      (getFrame (1+ n) (1+ p) (1+ q) (⇑₃ p≤q≤n) (D .₁)
      (getFrame (1+ n) (1+ q) (1+ n) (⇑₃ ◆₃' drop₃-1 p≤q≤n) (D .₁)
         (νFace (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁)) .₂ ω)
      ≡⟨ cong (λ - → getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _ (- .₂ ω))
              (getFrame-compose (1+ n) (1+ p) (1+ n) (1+ q) (◆₄' ⇑₃ p≤q≤n) (D .₁)
                (νFace (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁)) ⟩
    νFace n p (drop₃-2 p≤q≤n) ω (D .₁)
      (νFace (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁) ∎

  painting-≡ : ∀ n p {δ} (p≤n≤n : [ p ≤ n ≤ n ][ δ ]₃)
             → (D : νSet-< n) (E : νSet-= n D)
             → (d d' : frame n p (drop₃-2 p≤n≤n) D .Dom)
             → (c : painting n p (drop₃-2 p≤n≤n) D E d .Dom)
             → (c' : painting n p (drop₃-2 p≤n≤n) D E d' .Dom)
             → (getPainting n p n p≤n≤n D E d c ≡ getPainting n p n p≤n≤n D E d' c')
             → Σ-≡ (d , c) (d' , c')
  painting-≡ n p {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) D E d d' c c' eq
    with recover-nat-eq p n Hpq | recover-nat-eq δqn δpn Hpqn
  ... | refl | refl = ≡→Σ-≡ eq
  painting-≡ n p {1+ δ} (ineq₃ (1+ δpn) δqn hpq hpn hqn hpqn) D E d d' (l , c) (l' , c') eq =
    let 1+p≤q≤n = ineq₃ δpn δqn hpq hpn hqn hpqn in
    Σ-≡-assoc (painting-≡ n (1+ p) {δ} 1+p≤q≤n D E (d , l) (d' , l') c c' eq)
  
  layer-≡ : ∀ n p {δ} (p≤n : [ 1+ p ≤ 1+ n ][ δ ]₂)
          → (D : νSet-< (1+ n))
          → (ε : arity)
          → (d d' : frame (1+ n) (1+ n) (◆₂ (1+ n)) D .Dom)
          → (H : getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₁ ≡
                 getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d' .₁)
          → (νFace n p (⇓₂ p≤n) ε D d ≡ νFace n p (⇓₂ p≤n) ε D d')
          → subst (λ - → layer (1+ n) p p≤n D - .Dom) H (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂) ε
          ≡ getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d' .₂ ε
  layer-≡ n p p≤n D ε d d' H H' =
    subst (λ - → layer (1+ n) p p≤n D - .Dom) H
      (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂) ε
     ≡⟨ subst-application (λ - → layer (1+ n) p p≤n _ - .Dom) (λ -₁ -₂ → -₂ ε) H ⟩⁻¹
    subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) (restr-frame n p p _ ε D -) .Dom) H
      (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε)
     ≡⟨ subst-∘ H _ ⟩
    subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) - .Dom)
      (cong (restr-frame n p p _ ε D) H)
      (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε)
     ≡⟨ cong (λ - → subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) - .Dom) -
                          (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε))
             (frame n p (⇓₂ p≤n) (D .₁) .has-UIP _ _ _ _) ⟩
    subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) - .Dom)
      (painting-≡ n p (◆₃' ⇓₂ p≤n) (D .₁) (D .₂) _ _ _ _ H' .₁)
      (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε)
     ≡⟨ painting-≡ n p (◆₃' ⇓₂ p≤n) (D .₁) (D .₂) _ _
         (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε)
         (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d' .₂ ε)
         H' .₂ ⟩
    getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d' .₂ ε ∎
  
  frame-≡ : ∀ n p {δ} (p≤n : [ p ≤ 1+ n ][ δ ]₂)
          → (D : νSet-< (1+ n))
          → (d d' : frame (1+ n) (1+ n) (◆₂ (1+ n)) D .Dom)
          → (∀ p {δ} (p≤n : [ p ≤ n ][ δ ]₂) (ε : arity) → νFace n p p≤n ε D d ≡ νFace n p p≤n ε D d')
          → getFrame (1+ n) p (1+ n) (◆₃' p≤n) D d ≡ getFrame (1+ n) p (1+ n) (◆₃' p≤n) D d'
  frame-≡ n zero   p≤n D d d' f = refl
  frame-≡ n (1+ p) p≤n D d d' f =
   let rec = frame-≡ n p (↓₂ p≤n) D d d' f in 
   Σ-≡→≡ (rec , funExt λ ε → layer-≡ n p p≤n D ε d d' rec (f p (⇓₂ p≤n) ε))
  
  
  νFace-≡ : ∀ n (D : νSet-< (1+ n))
         → (d d' : frame (1+ n) (1+ n) (◆₂ 1+ n) D .Dom)
         → (∀ p {δ} (p≤n : [ p ≤ n ][ δ ]₂) (ε : arity) → νFace n p p≤n ε D d ≡ νFace n p p≤n ε D d')
         → d ≡ d'
  νFace-≡ n D d d' eq = frame-≡ n (1+ n) (◆₂ (1+ n)) D d d' eq

νSet-F0-< : ∀ m → νSet-< m → F0-< m 
νSet-F0-< zero D = tt
νSet-F0-< (1+ m) (D , E) = (νSet-F0-< m D) , (TotalSpace D E)

νSet-Face-< : ∀ m → (D : νSet-< (1+ m))
            → Face-< m (νSet-F0-< (1+ m) D)
νSet-Face-< zero D = tt
νSet-Face-< (1+ m) (D , E) = νSet-Face-< m D ,  λ p p≤n ε d → νFace m p p≤n ε D (d .₁)

νSet-Coh-< : ∀ m → (D : νSet-< (2+ m))
         → Coh-< m (νSet-F0-< (2+ m) D) (νSet-Face-< (1+ m) D)
νSet-Coh-< zero   D = tt
νSet-Coh-< (1+ m) ((D , E) , E') = νSet-Coh-< m (D , E) , λ p q p≤q≤m ε ω d → νFace-coh m p q p≤q≤m ε ω (D , E) (d .₁)

νSet-psh-< : ∀ {m} → (D : νSet-< (2+ m)) → Presheaf-< m
νSet-psh-< D .F0 = νSet-F0-< _ D
νSet-psh-< D .Face = νSet-Face-< _ D
νSet-psh-< D .Coh = νSet-Coh-< _ D

νSet-F0-≥ : ∀ m → (D : νSet-< m) → νSet-> m D → ℕ → HSet
νSet-F0-≥ m D νSet 0      = TotalSpace D (νSet .this)
νSet-F0-≥ m D νSet (1+ n) = νSet-F0-≥ (1+ m) (D , νSet .this) (νSet .next) n

νSet-Face-> : ∀ m → (D : νSet-< m) (νSet : νSet-> m D)
            → ∀ n p {δ}
            → [ p ≤ n + m ][ δ ]₂ → arity
            → νSet-F0-≥ m D νSet (1+ n) .Dom
            → νSet-F0-≥ m D νSet n .Dom
νSet-Face-> m D νSet 0 p p≤m ε d = νFace m p p≤m ε (D , νSet .this) (d .₁)
νSet-Face-> m D νSet (1+ n) = νSet-Face-> (1+ m) (D , νSet .this) (νSet .next) n

νSet-Coh-> : ∀ m → (D : νSet-< m) (νSet : νSet-> m D)
            → ∀ n p q {δ}
            → (p≤q≤n : [ p ≤ q ≤ n + m ][ δ ]₃) 
            → (ε ω : arity)
            → (d : νSet-F0-≥ m D νSet (2+ n) .Dom)
            → νSet-Face-> m D νSet n q (drop₃-1 p≤q≤n) ε
               (νSet-Face-> m D νSet (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω d)
            ≡ νSet-Face-> m D νSet n p (drop₃-2 p≤q≤n) ω
               (νSet-Face-> m D νSet (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε d)
νSet-Coh-> m D νSet zero p q p≤q≤m ε ω d =  νFace-coh m p q p≤q≤m ε ω (_ , νSet .next .this) (d .₁)
νSet-Coh-> m D νSet (1+ n) = νSet-Coh-> (1+ m) (D , νSet .this) (νSet .next) n

νSet→zipper : ∀ m (D : νSet-< m) (νSet : νSet-> m D) → Presheaf-zipper m
νSet→zipper m D νSet .|F0-<| = νSet-F0-< m D
νSet→zipper m D νSet .|F0-≥| = νSet-F0-≥ m D νSet
νSet→zipper m D νSet .|Face-<| = νSet-Face-< m (D , νSet .this)
νSet→zipper m D νSet .|Face-≥| = νSet-Face-> m D νSet
νSet→zipper m D νSet .|Coh-<| = νSet-Coh-< m ((D , νSet .this) , νSet .next .this)
νSet→zipper m D νSet .|Coh-≥| = νSet-Coh-> m D νSet

g : νSet → Presheaf
g νSet .F0 = νSet-F0-≥ 0 tt νSet
g νSet .Face = νSet-Face-> 0 tt νSet
g νSet .Face-coh = νSet-Coh-> 0 tt νSet
