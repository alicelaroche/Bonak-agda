open import Prelude

module Inequalities where


_≡ℕ_ : ℕ → ℕ → Type
zero ≡ℕ zero = ⊤
zero ≡ℕ 1+ m = ⊥
1+ n ≡ℕ zero = ⊥
1+ n ≡ℕ 1+ m = n ≡ℕ m

≡ℕ-refl : ∀ n → n ≡ℕ n
≡ℕ-refl zero = tt
≡ℕ-refl (1+ n) = ≡ℕ-refl n

infix 4 _≡ℕ_

recover-nat-eq' : (n m : ℕ) → .(n ≡ℕ m) → n ≡ m
recover-nat-eq' zero zero n≡m = refl
recover-nat-eq' (1+ n) (1+ m) n≡m = cong suc (recover-nat-eq' n m n≡m)

recover-nat-eq'-refl : ∀ n → recover-nat-eq' n n (≡ℕ-refl n) ≡ refl
recover-nat-eq'-refl zero   = refl
recover-nat-eq'-refl (1+ n) = cong (cong suc) (recover-nat-eq'-refl n)

record [_≤_]₂ (p n : ℕ) : Type where
  eta-equality
  constructor ineq₂
  field
    δpn : ℕ
    .Hpn : p + δpn ≡ℕ n
open [_≤_]₂ public

record [_≤_≤_]₃ (p q n : ℕ) : Type where
  eta-equality
  constructor ineq₃
  field
    δpq δpn δqn : ℕ
    .Hpq  : p + δpq ≡ℕ q
    .Hpn  : p + δpn ≡ℕ n
    .Hqn  : q + δqn ≡ℕ n
    .Hpqn : δpq + δqn ≡ℕ δpn
open [_≤_≤_]₃ public

record [_≤_≤_≤_]₄ (p r q n : ℕ) : Type where
  eta-equality
  constructor ineq₄
  field
    δpr δpq δpn δrq δrn δqn : ℕ
    .Hpr  : p + δpr ≡ℕ r
    .Hpq  : p + δpq ≡ℕ q
    .Hpn  : p + δpn ≡ℕ n
    .Hrq  : r + δrq ≡ℕ q
    .Hrn  : r + δrn ≡ℕ n
    .Hqn  : q + δqn ≡ℕ n
    .Hprq : δpr + δrq ≡ℕ δpq
    .Hprn : δpr + δrn ≡ℕ δpn
    .Hpqn : δpq + δqn ≡ℕ δpn
    .Hrqn : δrq + δqn ≡ℕ δrn
open [_≤_≤_≤_]₄ public

drop₃-1 : ∀ {p q n} → [ p ≤ q ≤ n ]₃ → [ q ≤ n ]₂
drop₃-1 (ineq₃ _ _ δqn _ _ Hqn _) =
 ineq₂ δqn Hqn

drop₃-2 : ∀ {p q n} → [ p ≤ q ≤ n ]₃ → [ p ≤ n ]₂
drop₃-2 (ineq₃ _ δpn _ _ Hpn _ _) =
 ineq₂ δpn Hpn

drop₄-1 : ∀ {p r q n} → [ p ≤ r ≤ q ≤ n ]₄ → [ r ≤ q ≤ n ]₃
drop₄-1 (ineq₄ _ _ _ δrq δrn δqn _ _ _ Hrq Hrn Hqn _ _ _ Hrqn) =
 ineq₃ δrq δrn δqn Hrq Hrn Hqn Hrqn

drop₄-2 : ∀ {p r q n} → [ p ≤ r ≤ q ≤ n ]₄ → [ p ≤ q ≤ n ]₃
drop₄-2 (ineq₄ _ δpq δpn _ _ δqn _ Hpq Hpn _ _ Hqn _ _ Hpqn _) =
 ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn

drop₄-3 : ∀ {p r q n} → [ p ≤ r ≤ q ≤ n ]₄ → [ p ≤ r ≤ n ]₃
drop₄-3 (ineq₄ δpr _ δpn _ δrn _ Hpr _ Hpn _ Hrn _ _ Hprn _ _) =
 ineq₃ δpr δpn δrn Hpr Hpn Hrn Hprn

◆₂_ : ∀ n → [ n ≤ n ]₂
◆₂ n = ineq₂ 0 (≡ℕ-refl n)

◆₃_ : ∀ {p n} → [ p ≤ n ]₂ → [ p ≤ p ≤ n ]₃
◆₃_ {p} (ineq₂ δpn Hpn) = ineq₃ 0 δpn δpn (≡ℕ-refl p) Hpn Hpn (≡ℕ-refl δpn)

◆₃'_ : ∀ {p n} → [ p ≤ n ]₂ → [ p ≤ n ≤ n ]₃
◆₃'_ {p} {n} (ineq₂ δpn Hpn) = ineq₃ δpn δpn 0 Hpn Hpn (≡ℕ-refl n) (≡ℕ-refl δpn)

◆₄_ : ∀ {p q n} → [ p ≤ q ≤ n ]₃ → [ p ≤ p ≤ q ≤ n ]₄
◆₄_ {p} (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) =
 ineq₄ 0 δpq δpn δpq δpn δqn (≡ℕ-refl p) Hpq Hpn Hpq Hpn Hqn (≡ℕ-refl δpq) (≡ℕ-refl δpn) Hpqn Hpqn

◆₄'_ : ∀ {p q n} → [ p ≤ q ≤ n ]₃ → [ p ≤ q ≤ n ≤ n ]₄
◆₄'_ {p} {q} {n} (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) =
 ineq₄ δpq δpn δpn δqn δqn 0 Hpq Hpn Hpn Hqn Hqn (≡ℕ-refl n) Hpqn Hpqn (≡ℕ-refl δpn) (≡ℕ-refl δqn)

↓₂_ : ∀ {p n} → [ 1+ p ≤ n ]₂ → [ p ≤ n ]₂
↓₂ ineq₂ δpn Hpn = ineq₂ (1+ δpn) Hpn

⇓₂_ : ∀ {p n} → [ 1+ p ≤ 1+ n ]₂ → [ p ≤ n ]₂
⇓₂ ineq₂ δpn Hpn = ineq₂ δpn Hpn

↑₂_ : ∀ {p n} → [ p ≤ n ]₂ → [ p ≤ 1+ n ]₂
↑₂ ineq₂ δpn Hpn = ineq₂ (1+ δpn) Hpn

⇑₂_ : ∀ {p n} → [ p ≤ n ]₂ → [ 1+ p ≤ 1+ n ]₂
⇑₂ ineq₂ δpn Hpn = ineq₂ δpn Hpn

↓₃_ : ∀ {p q n} → [ 1+ p ≤ q ≤ n ]₃ → [ p ≤ q ≤ n ]₃
↓₃ ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ (1+ δpq) (1+ δpn) δqn Hpq Hpn Hqn Hpqn

↓₃'_ : ∀ {p q n} → [ 1+ p ≤ 1+ q ≤ n ]₃ → [ p ≤ q ≤ n ]₃
↓₃' ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ δpq (1+ δpn) (1+ δqn) Hpq Hpn Hqn Hpqn

⇓₃_ : ∀ {p q n} → [ 1+ p ≤ 1+ q ≤ 1+ n ]₃ → [ p ≤ q ≤ n ]₃
⇓₃ ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn =
 ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn
 
↑₃_ : ∀ {p q n} → [ p ≤ q ≤ n ]₃ → [ p ≤ q ≤ 1+ n ]₃
↑₃ ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ δpq (1+ δpn) (1+ δqn) Hpq Hpn Hqn Hpqn

↑₃'_ : ∀ {p q n} → [ p ≤ q ≤ n ]₃ → [ p ≤ 1+ q ≤ 1+ n ]₃
↑₃' ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ (1+ δpq) (1+ δpn) δqn Hpq Hpn Hqn Hpqn

⇑₃_ : ∀ {p q n} → [ p ≤ q ≤ n ]₃ → [ 1+ p ≤ 1+ q ≤ 1+ n ]₃
⇑₃ ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn =
 ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn
 
↓₄_ : ∀ {p r q n} → [ 1+ p ≤ r ≤ q ≤ n ]₄ → [ p ≤ r ≤ q ≤ n ]₄
↓₄ ineq₄ δpr δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn =
  ineq₄ (1+ δpr) (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn

⇓₄_ : ∀ {p r q n} → [ 1+ p ≤ 1+ r ≤ 1+ q ≤ 1+ n ]₄ → [ p ≤ r ≤ q ≤ n ]₄ 
⇓₄ ineq₄ δpr δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn =
  ineq₄ δpr δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn

--examples of induction, not usable in practice

variable
  ℓ : Level

≤₂-ind : ∀ p n (p≤n : [ p ≤ n ]₂)
       → (P : ∀ p → [ p ≤ n ]₂ → Type ℓ)
       → (base : P n (◆₂ n))
       → (rec : ∀ p → (p<n : [ 1+ p ≤ n ]₂) → P (1+ p) p<n → P p (↓₂ p<n))
       → P p p≤n
≤₂-ind p n p≤n P base rec = I p (p≤n .δpn) p≤n refl
  where
  I : ∀ p δ (p≤n : [ p ≤ n ]₂)
    → δ ≡ p≤n .δpn
    → P p p≤n
  I p zero (ineq₂ δpn Hpn) refl with recover-nat-eq' p n Hpn
  ... | refl = base
  I p (1+ δ) (ineq₂ _ Hpn) refl =
    let 1+p≤n = ineq₂ δ Hpn in
    rec p 1+p≤n (I (1+ p) δ 1+p≤n refl)

≤₃-ind : ∀ p q n (p≤q≤n : [ p ≤ q ≤ n ]₃)
       → (P : ∀ p q → [ p ≤ q ≤ n ]₃ → Type ℓ)
       → (base : ∀ q (q≤n : [ q ≤ n ]₂) → P q q (◆₃ q≤n))
       → (rec : ∀ p q → (p≤q<n : [ 1+ p ≤ 1+ q ≤ n ]₃)
                      → P (1+ p) (1+ q) p≤q<n → P p (1+ q) (↓₃ p≤q<n))
       → P p q p≤q≤n
≤₃-ind p q n p≤q≤n P base rec = II p q (p≤q≤n .δpq) p≤q≤n refl
  where
  II : ∀ p q δ (p≤q≤n : [ p ≤ q ≤ n ]₃)
    → δ ≡ p≤q≤n .δpq
    → P p q p≤q≤n
  II p q zero (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn) refl with
    recover-nat-eq' p q Hpq | recover-nat-eq' δqn δpn Hpqn
  ... | refl | refl = base q (ineq₂ δpn Hpn)
  II p (1+ q) (1+ δ) (ineq₃ _ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) refl =
      let 1+p≤q≤n = ineq₃ δ δpn δqn Hpq Hpn Hqn Hpqn in
      rec p q 1+p≤q≤n (II (1+ p) (1+ q) δ 1+p≤q≤n refl)

≤₄-ind : ∀ p r q n (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄)
       → (P : ∀ p r q → [ p ≤ r ≤ q ≤ n ]₄ → Type ℓ)
       → (base : ∀ r q (r≤q≤n : [ r ≤ q ≤ n ]₃) → P r r q (◆₄ r≤q≤n))
       → (rec : ∀ p r q
              → (p≤r≤q<n : [ 1+ p ≤ 1+ r ≤ 1+ q ≤ n ]₄)
              → P (1+ p) (1+ r) (1+ q) p≤r≤q<n
              → P p (1+ r) (1+ q) (↓₄ p≤r≤q<n))
       → P p r q p≤r≤q≤n
≤₄-ind p r q n p≤r≤q≤n P base rec = III p r q (p≤r≤q≤n .δpr) p≤r≤q≤n refl 
  where
  III : ∀ p r q δ (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ]₄)
    → δ ≡ p≤r≤q≤n .δpr
    → P p r q p≤r≤q≤n
  III p r q 0 (ineq₄ δpr δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn)
    refl with recover-nat-eq' p r Hpr | recover-nat-eq' δrq δpq Hprq | recover-nat-eq' δrn δpn Hprn
  ... | refl | refl | refl = base r q (ineq₃ δpq δpn δqn Hpq Hpn Hqn Hpqn)
  III p (1+ r) (1+ q) (1+ δ) (ineq₄ _ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn)
    refl =
    let 1+p≤r≤q≤n = ineq₄ δ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn in
    rec p r q 1+p≤r≤q≤n (III (1+ p) (1+ r) (1+ q) δ 1+p≤r≤q≤n refl)
