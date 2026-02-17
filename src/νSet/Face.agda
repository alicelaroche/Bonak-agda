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

getFrame : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃)
         → (D : νSet-< n)
         → frame n q (drop₃-1 p≤q≤n) D .Dom
         → frame n p (drop₃-2 p≤q≤n) D .Dom
getFrame n p q p≤q≤n D = helper p q _ p≤q≤n refl
 where
 helper : ∀ p q δ → (p≤q≤n : [ p ≤ q ≤ n ]₃)
        → δ ≡ p≤q≤n .δpq
        → frame n q (drop₃-1 p≤q≤n) D .Dom
        → frame n p (drop₃-2 p≤q≤n) D .Dom
 helper p q zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl d
   with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
 ... | refl | refl = d
 helper p q (1+ δ) (ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl d =
   let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
   helper (1+ p) q δ 1+p≤q≤n refl d .₁

getPainting : ∀ n p q (p≤q≤n : [ p ≤ q ≤ n ]₃)
            → (D : νSet-< n) (E : νSet-= n D)
            → (d : frame n p (drop₃-2 p≤q≤n) D .Dom)
            → (c : painting n p (drop₃-2 p≤q≤n) D E d .Dom)
            → Σ[ d ∈ frame n q (drop₃-1 p≤q≤n) D .Dom ]
              painting n q (drop₃-1 p≤q≤n) D E d .Dom
getPainting n p q p≤q≤n D E = helper p q _ p≤q≤n refl
 where
 helper : ∀ p q δ → (p≤q≤n : [ p ≤ q ≤ n ]₃)
        → δ ≡ p≤q≤n .δpq
        → (d : frame n p (drop₃-2 p≤q≤n) D .Dom)
        → (c : painting n p (drop₃-2 p≤q≤n) D E d .Dom)
        → Σ[ d ∈ frame n q (drop₃-1 p≤q≤n) D .Dom ]
          painting n q (drop₃-1 p≤q≤n) D E d .Dom
 helper p q zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl d c
   with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
 ... | refl | refl = d , c
 helper p q (1+ δ) (ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl d (l , c) =
   let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
   helper (1+ p) q δ 1+p≤q≤n refl (d , l) c

getFrame-compose : ∀ n p q r → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄) 
                 → (D : νSet-< n)
                 → (d : frame n q (drop₃-1 (drop₄-1 p≤r≤q≤n)) D .Dom)
                 → getFrame n p r (drop₄-3 p≤r≤q≤n) D (
                   getFrame n r q (drop₄-1 p≤r≤q≤n) D d)
                 ≡ getFrame n p q (drop₄-2 p≤r≤q≤n) D d
getFrame-compose n p q r p≤r≤q≤n D = helper _ _ _ _ p≤r≤q≤n refl
  where
  helper : ∀ p q r δ → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄)
          → δ ≡ p≤r≤q≤n .δpr
          → (d : frame n q (drop₃-1 (drop₄-1 p≤r≤q≤n)) D .Dom)
          → getFrame n p r (drop₄-3 p≤r≤q≤n) D (
            getFrame n r q (drop₄-1 p≤r≤q≤n) D d)
          ≡ getFrame n p q (drop₄-2 p≤r≤q≤n) D d
  helper p q r zero (ineq₄ _ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) refl d
    with recover-nat-eq' p r Hpr | recover-nat-eq' δrq δpq Hprq | recover-nat-eq' δrn δpn Hprn
  ... | refl | refl | refl = refl
  helper p (1+ q) (1+ r) (1+ δ) (ineq₄ _ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) refl d =
    let 1+p≤r≤q≤n = ineq₄ δ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn  in
    cong (λ - → - .₁) (helper (1+ p) (1+ q) (1+ r) δ 1+p≤r≤q≤n refl d)

getFrame-getPainting : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃) 
                     → (D : νSet-< n) (E : νSet-= n D)
                     → (d : frame n p (drop₃-2 p≤q≤n) D .Dom)
                     → (c : painting n p (drop₃-2 p≤q≤n) D E d .Dom)           
                     → getFrame n p q p≤q≤n D (getPainting n p q p≤q≤n D E d c .₁)
                     ≡ d
getFrame-getPainting n p q p≤q≤n D E = helper p q _ p≤q≤n refl
 where
 helper : ∀ p q δ → (p≤q≤n : [ p ≤ q ≤ n ]₃)
        → δ ≡ p≤q≤n .δpq
        → (d : frame n p (drop₃-2 p≤q≤n) D .Dom)
        → (c : painting n p (drop₃-2 p≤q≤n) D E d .Dom)
        → getFrame n p q p≤q≤n D (getPainting n p q p≤q≤n D E d c .₁)
        ≡ d
 helper p q zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl d c
   with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
 ... | refl | refl = refl 
 helper p q (1+ δ) (ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl d (l , c) =
   let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
   cong (λ - → - .₁) (helper (1+ p) q δ 1+p≤q≤n refl (d , l) c)

getFrame-getPainting' : ∀ n p q r → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄) 
                     → (D : νSet-< n) (E : νSet-= n D)
                     → (d : frame n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
                     → (c : painting n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) D E d .Dom)
                     → getFrame n r q (drop₄-1 p≤r≤q≤n) D
                         (getPainting n p q (drop₄-2 p≤r≤q≤n) D E d c .₁)
                     ≡ getPainting n p r (drop₄-3 p≤r≤q≤n) D E d c .₁
getFrame-getPainting' n p q r p≤r≤q≤n D E = helper _ _ _ _ p≤r≤q≤n refl
  where
  helper : ∀ p q r δ → (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄) 
         → δ ≡ p≤r≤q≤n .δpr
         → (d : frame n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) D .Dom)
         → (c : painting n p (drop₃-2 (drop₄-2 p≤r≤q≤n)) D E d .Dom)
         → getFrame n r q (drop₄-1 p≤r≤q≤n) D
             (getPainting n p q (drop₄-2 p≤r≤q≤n) D E d c .₁)
         ≡ getPainting n p r (drop₄-3 p≤r≤q≤n) D E d c .₁
  helper p q r zero p≤p≤q≤n@(ineq₄ _ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) refl d c
    with recover-nat-eq' p r Hpr | recover-nat-eq' δrq δpq Hprq | recover-nat-eq' δrn δpn Hprn
  ... | refl | refl | refl = getFrame-getPainting n p q (drop₄-1 p≤p≤q≤n) D E d c
  helper p q r (1+ δ) (ineq₄ _ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) refl d (l , c) =
    let 1+p≤r≤q≤n = ineq₄ δ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn  in
     helper (1+ p) q r δ 1+p≤r≤q≤n refl (d , l) c

getFrameRestr : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃) 
              → (ε : arity)
              → (D : νSet-< (1+ n))
              → (d : frame (1+ n) q (↑₂ drop₃-1 p≤q≤n) D .Dom)
              → getFrame n p q p≤q≤n (D .₁) (restr-frame n q q (◆₃ drop₃-1 p≤q≤n) ε D d)
              ≡ restr-frame n p q p≤q≤n ε D (getFrame (1+ n) p q (↑₃ p≤q≤n) D d)
getFrameRestr n p q p≤q≤n ε D = helper p q _ p≤q≤n refl
 where
 helper : ∀ p q δ → (p≤q≤n : [ p ≤ q ≤ n ]₃)
        → δ ≡ p≤q≤n .δpq
        → (d : frame (1+ n) q (↑₂ drop₃-1 p≤q≤n) D .Dom)
        → getFrame n p q p≤q≤n (D .₁) (restr-frame n q q (◆₃ drop₃-1 p≤q≤n) ε D d)
        ≡ restr-frame n p q p≤q≤n ε D (getFrame (1+ n) p q (↑₃ p≤q≤n) D d)
 helper p q zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl d
   with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
 ... | refl | refl = refl 
 helper p (1+ q) (1+ δ) p≤q≤n@(ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl d =
   let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
   cong (λ - → - .₁) (helper (1+ p) (1+ q) _ 1+p≤q≤n refl d) 

getPaintingRestr : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃) 
                 → (ε : arity)
                 → (D : νSet-< (1+ n)) (E : νSet-= (1+ n) D)
                 → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
                 → (c : painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D E d .Dom)
                 → getPainting n q n (◆₃' drop₃-1 p≤q≤n) (D .₁) (D .₂) _
                     (getPainting (1+ n) p (1+ q) (↑₃' p≤q≤n) D E d c .₁ .₂ ε)
                 ≡ getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁) (D .₂) _
                     (restr-painting n p q p≤q≤n ε D E d c) 
getPaintingRestr n p q p≤q≤n ε D E = helper p q _ p≤q≤n refl
 where
 helper : ∀ p q δ → (p≤q≤n : [ p ≤ q ≤ n ]₃)
        → δ ≡ p≤q≤n .δpq
        → (d : frame (1+ n) p (↑₂ drop₃-2 p≤q≤n) D .Dom)
        → (c : painting (1+ n) p (↑₂ drop₃-2 p≤q≤n) D E d .Dom)
        → getPainting n q n (◆₃' drop₃-1 p≤q≤n) (D .₁) (D .₂) _
            (getPainting (1+ n) p (1+ q) (↑₃' p≤q≤n) D E d c .₁ .₂ ε)
        ≡ getPainting n p n (◆₃' drop₃-2 p≤q≤n) (D .₁) (D .₂) _
            (restr-painting n p q p≤q≤n ε D E d c)
 helper p q zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl d c
   with recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
 ... | refl | refl = refl
 helper p (1+ q) (1+ δ) p≤q≤n@(ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl d (l , c) =
   let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
   helper (1+ p) (1+ q) _ 1+p≤q≤n refl (d , l) c

Face : ∀ n p (p≤n : [ p ≤ n ]₂) → arity
     → (D : νSet-< (1+ n))
     → (d : frame (1+ n) (1+ n) (◆₂ 1+ n) D .Dom)
     → Σ[ d ∈ frame n n (◆₂ n) (D .₁) .Dom ]
      (painting n n (◆₂ n) (D .₁) (D .₂) d .Dom)
Face n p p≤n ε D d =
 getPainting n p n (◆₃' p≤n) (D .₁) (D .₂) _
   (getFrame (1+ n) (1+ p) (1+ n) (⇑₃ ◆₃' p≤n) D d .₂ ε)

Face-coh : ∀ n p q → (p≤q≤n : [ p ≤ q ≤ n ]₃) 
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
              (Face (1+ n) (1+ q) (ineq₂ (p≤q≤n .δqn) _) ε D d .₁)) ⟩
  Face n p (drop₃-2 p≤q≤n) ω (D .₁)
    (Face (1+ n) (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D d .₁) ∎

painting-≡ : ∀ n p (p≤n : [ p ≤ n ]₂)
           → (D : νSet-< n) (E : νSet-= n D)
           → (d d' : frame n p p≤n D .Dom)
           → (c : painting n p p≤n D E d .Dom)
           → (c' : painting n p p≤n D E d' .Dom) 
           → (getPainting n p n (◆₃' p≤n) D E d c ≡ getPainting n p n (◆₃' p≤n) D E d' c')
           → Σ-≡ (d , c) (d' , c')
painting-≡ n p p≤n D E d d' c c' eq = helper p _ (◆₃' p≤n) refl d d' c c' (≡→Σ-≡ eq)
 where
  helper : ∀ p δ (p≤n≤n : [ p ≤ n ≤ n ]₃)
         → δ ≡ p≤n≤n .δpq
         → (d d' : frame n p (drop₃-2 p≤n≤n) D .Dom)
         → (c : painting n p (drop₃-2 p≤n≤n) D E d .Dom)
         → (c' : painting n p (drop₃-2 p≤n≤n) D E d' .Dom)
         → (Σ-≡ (getPainting n p n p≤n≤n D E d c) (getPainting n p n p≤n≤n D E d' c'))
         → Σ-≡ (d , c) (d' , c')
  helper p zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl d d' c c' eq
    with recover-nat-eq' p n Hpq | recover-nat-eq' δqn δpn Hpqn
  ... | refl | refl = eq
  helper p (1+ δ) (ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl d d' (l , c) (l' , c') eq =
    let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
    Σ-≡-assoc (helper (1+ p) δ 1+p≤q≤n refl (d , l) (d' , l') c c' eq)

frame-≡ : ∀ n p (p≤n : [ p ≤ 1+ n ]₂)
        → (D : νSet-< (1+ n))
        → (d d' : frame (1+ n) (1+ n) (◆₂ (1+ n)) D .Dom)
        → (∀ p (p≤n : [ p ≤ n ]₂) (ε : arity) → Face n p p≤n ε D d ≡ Face n p p≤n ε D d')
        → getFrame (1+ n) p (1+ n) (◆₃' p≤n) D d ≡ getFrame (1+ n) p (1+ n) (◆₃' p≤n) D d'
frame-≡ n zero   p≤n D d d' f = refl
frame-≡ n (1+ p) p≤n D d d' f = Σ-≡→≡ (frame-≡ n p (↓₂ p≤n) D d d' f , fe _ _ helper)
  where
    helper : ∀ ε → subst (λ - → layer (1+ n) p _ D - .Dom) (frame-≡ n p (↓₂ p≤n) D d d' f)
                     (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂) ε
                 ≡ getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d' .₂ ε
    helper ε =
      subst (λ - → layer (1+ n) p _ D - .Dom)
        (frame-≡ n p (↓₂ p≤n) D d d' f)
        (getFrame (1+ n) (1+ p) (1+ n) (◆₃' p≤n) D d .₂) ε
        ≡⟨ subst-application (λ - → layer (1+ n) p _ _ - .Dom) (λ -₁ -₂ → -₂ ε)
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
       → (∀ p (p≤n : [ p ≤ n ]₂) (ε : arity) → Face n p p≤n ε D d ≡ Face n p p≤n ε D d')
       → d ≡ d'
Face-≡ n D d d' eq = helper (frame-≡ n (1+ n) (◆₂ (1+ n)) D d d' eq)
 where
 helper : getFrame (1+ n) (1+ n) (1+ n) (◆₃' (◆₂ 1+ n)) D d
        ≡ getFrame (1+ n) (1+ n) (1+ n) (◆₃' (◆₂ 1+ n)) D d'
        → d ≡ d'
 helper eq rewrite recover-nat-eq'-refl (1+ n) = eq

{-
X-aux : ∀ (k n : ℕ)
      → (D : νSet-< n) → νSet-> n D
      → HSet
X-aux zero   n D νSet = HΣ[ d ∈ frame n n (◆₂ n) D ] painting n n (◆₂ n) D (νSet .this) d
X-aux (1+ k) n D νSet = X-aux k (1+ n) (D , (νSet .this)) (νSet .next)

Face-aux : ∀ (k n p : ℕ) → [ p ≤ k + n ]₂
         → arity
         → (D : νSet-< n) (νSet : νSet-> n D)
         → X-aux (1+ k) n D νSet .Dom
         → X-aux k n D νSet .Dom
Face-aux zero n p p≤k+n ε D νSet (d , c) =
 Face-base n p p≤k+n ε (D , νSet .this) d
Face-aux (1+ k) n p p≤k+n ε D νSet X =
 Face-aux k (1+ n) p p≤k+n ε _ (νSet .next) X

Face-aux-coh : ∀ k n p q → (p≤q≤n : [ p ≤ q ≤ k + n ]₃) 
             → (ε ω : arity)
             → (D : νSet-< n) (νSet : νSet-> n D)
             → (X : X-aux (2+ k) n D νSet .Dom)
             → Face-aux k n q (drop₃-1 p≤q≤n) ε D νSet
                (Face-aux (1+ k) n p (↑₂ drop₃-2 p≤q≤n) ω D νSet X )
             ≡ Face-aux k n p (drop₃-2 p≤q≤n) ω D νSet
                (Face-aux (1+ k) n (1+ q) (⇑₂ drop₃-1 p≤q≤n) ε D νSet X )
Face-aux-coh zero n p q p≤q≤n ε ω D νSet (d , c) =
 Face-base-coh n p q p≤q≤n ε ω _ d
Face-aux-coh (1+ k) n p q p≤q≤n ε ω D νSet X =
 Face-aux-coh k (1+ n) p q p≤q≤n ε ω _ (νSet .next) X
-}
