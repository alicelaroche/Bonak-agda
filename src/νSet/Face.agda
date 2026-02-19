open import Prelude

module νSet.Face
    (fe : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
      → (f g : (a : A) → B a)
      → (∀ a → f a ≡ g a)
      → f ≡ g)
  (fe-≡ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
        → (f g : (a : A) → B a)
        → (p : f ≡ g)
        → fe f g (λ a → cong-app p a) ≡ p)
  (arity : Type)
 where

open import Inequalities
open import HSet
open HΠ fe fe-≡

open import νSet.Base fe fe-≡ arity

getFrame : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
         → (D : νSet-< n)
         → frame n q (drop₃-1 p≤q≤n) D .Dom
         → frame n p (drop₃-2 p≤q≤n) D .Dom
getFrame n p q {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) D d
  with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
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
  with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
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
  with recover-nat-eq' p r Hpr | recover-nat-eq' δrq δpq Hprq | recover-nat-eq' δrn δpn Hprn
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
  with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
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
  with recover-nat-eq' p r Hpr | recover-nat-eq' δrq δpq Hprq | recover-nat-eq' δrn δpn Hprn
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
  with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
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
  with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
... | refl | refl = refl
getPaintingRestr n p (1+ q) {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) ε D E d (l , c) =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  getPaintingRestr n (1+ p) (1+ q) {δ} 1+p≤q≤n ε D E (d , l) c

Face : ∀ n p {δ} (p≤n : [ p ≤ n ][ δ ]₂) → arity
     → (D : νSet-< (1+ n))
     → (d : frame (1+ n) (1+ n) (◆₂ 1+ n) D .Dom)
     → Σ[ d ∈ frame n n (◆₂ n) (D .₁) .Dom ]
      (painting n n (◆₂ n) (D .₁) (D .₂) d .Dom)
Face n p p≤n ε D d =
 getPainting n p n (◆₃' p≤n) (D .₁) (D .₂) _
   (getFrame (1+ n) (1+ p) (1+ n) (⇑₃ ◆₃' p≤n) D d .₂ ε)

Face-coh : ∀ n p q {δ} → (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃) 
         → (ε ω : arity)
         → (D : νSet-< (2+ n))
         → (d : frame (2+ n) (2+ n) (◆₂ 2+ n) D .Dom)
         → Face n q (drop₃-1 p≤q≤n) ε (D .₁)
             (Face (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω D d .₁)
         ≡ Face n p (drop₃-2 p≤q≤n) ω (D .₁)
             (Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁)
Face-coh n p q p≤q≤n ε ω D d =
  Face n q (drop₃-1 p≤q≤n) ε (D .₁)
    (Face (1+ n) p (↑₂ drop₃-2 p≤q≤n) ω D d .₁)
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
       (Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁)) .₂ ω)
    ≡⟨ cong (λ - → getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁ .₁) (D .₁ .₂) _ (- .₂ ω))
            (getFrame-compose (1+ n) (1+ p) (1+ n) (1+ q) (◆₄' ⇑₃ p≤q≤n) (D .₁)
              (Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁)) ⟩
  Face n p (drop₃-2 p≤q≤n) ω (D .₁)
    (Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁) ∎

painting-≡ : ∀ n p {δ} (p≤n : [ p ≤ n ][ δ ]₂)
           → (D : νSet-< n) (E : νSet-= n D)
           → (d d' : frame n p p≤n D .Dom)
           → (c : painting n p p≤n D E d .Dom)
           → (c' : painting n p p≤n D E d' .Dom) 
           → (getPainting n p n (◆₃' p≤n) D E d c ≡ getPainting n p n (◆₃' p≤n) D E d' c')
           → Σ-≡ (d , c) (d' , c')
painting-≡ n p p≤n D E d d' c c' eq = helper p _ (◆₃' p≤n) d d' c c' (≡→Σ-≡ eq)
 where
  helper : ∀ p δ (p≤n≤n : [ p ≤ n ≤ n ][ δ ]₃)
         → (d d' : frame n p (drop₃-2 p≤n≤n) D .Dom)
         → (c : painting n p (drop₃-2 p≤n≤n) D E d .Dom)
         → (c' : painting n p (drop₃-2 p≤n≤n) D E d' .Dom)
         → (Σ-≡ (getPainting n p n p≤n≤n D E d c) (getPainting n p n p≤n≤n D E d' c'))
         → Σ-≡ (d , c) (d' , c')
  helper p zero (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) d d' c c' eq
    with recover-nat-eq' p n Hpq | recover-nat-eq' δqn δpn Hpqn
  ... | refl | refl = eq
  helper p (1+ δ) (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) d d' (l , c) (l' , c') eq =
    let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
    Σ-≡-assoc (helper (1+ p) δ 1+p≤q≤n (d , l) (d' , l') c c' eq)

frame-≡ : ∀ n p {δ} (p≤n : [ p ≤ 1+ n ][ δ ]₂)
        → (D : νSet-< (1+ n))
        → (d d' : frame (1+ n) (1+ n) (◆₂ (1+ n)) D .Dom)
        → (∀ p {δ} (p≤n : [ p ≤ n ][ δ ]₂) (ε : arity) → Face n p p≤n ε D d ≡ Face n p p≤n ε D d')
        → getFrame (1+ n) p (1+ n) (◆₃' p≤n) D d ≡ getFrame (1+ n) p (1+ n) (◆₃' p≤n) D d'
frame-≡ n zero   p≤n D d d' f = refl
frame-≡ n (1+ p) p≤n D d d' f = Σ-≡→≡ (frame-≡ n p (↓₂ p≤n) D d d' f , fe _ _ helper)
  where
    helper : ∀ ε → subst (λ - → layer (1+ n) p p≤n D - .Dom) (frame-≡ n p (↓₂ p≤n) D d d' f)
                     (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂) ε
                 ≡ getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d' .₂ ε
    helper ε =
      subst (λ - → layer (1+ n) p p≤n D - .Dom)
        (frame-≡ n p (↓₂ p≤n) D d d' f)
        (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂) ε
        ≡⟨ subst-application (λ - → layer (1+ n) p p≤n _ - .Dom) (λ -₁ -₂ → -₂ ε)
            (frame-≡ n p (↓₂ p≤n) D d d' f) ⟩⁻¹
      subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) (restr-frame n p p _ ε D -) .Dom)
         (frame-≡ n p (↓₂ p≤n) D d d' f)
         (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε)
        ≡⟨ subst-∘ (frame-≡ n p (↓₂ p≤n) D d d' f) ⟩
      subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) - .Dom)
         (cong (restr-frame n p p _ ε D) (frame-≡ n p (↓₂ p≤n) D d d' f))
         (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε)
        ≡⟨ cong (λ - → subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) - .Dom) -
                         (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε))
           (frame n p (⇓₂ p≤n) (D .₁) .has-UIP _ _ _ _) ⟩
      subst (λ - → painting n p (⇓₂ p≤n) (D .₁) (D .₂) - .Dom)
       (painting-≡ n p (⇓₂ p≤n) (D .₁) (D .₂) _ _ _ _ (f p (⇓₂ p≤n) ε) .₁)
       (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂ ε)
        ≡⟨ painting-≡ n p (⇓₂ p≤n) (D .₁) (D .₂) _ _ _ _ (f p (⇓₂ p≤n) ε) .₂ ⟩
      getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d' .₂ ε ∎

Face-≡ : ∀ n (D : νSet-< (1+ n)) (d d' : frame (1+ n) (1+ n) (◆₂ 1+ n) D .Dom)
       → (∀ p {δ} (p≤n : [ p ≤ n ][ δ ]₂) (ε : arity) → Face n p p≤n ε D d ≡ Face n p p≤n ε D d')
       → d ≡ d'
Face-≡ n D d d' eq = helper (frame-≡ n (1+ n) (◆₂ (1+ n)) D d d' eq)
 where
 helper : getFrame (1+ n) (1+ n) (1+ n) (◆₃' (◆₂ 1+ n)) D d
        ≡ getFrame (1+ n) (1+ n) (1+ n) (◆₃' (◆₂ 1+ n)) D d'
        → d ≡ d'
 helper eq rewrite recover-nat-eq'-refl (1+ n) = eq
