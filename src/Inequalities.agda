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

recover-nat-eq : (n m : ℕ) → .(n ≡ℕ m) → n ≡ m
recover-nat-eq zero zero n≡m = refl
recover-nat-eq (1+ n) (1+ m) n≡m = cong suc (recover-nat-eq n m n≡m)

recover-nat-eq-refl : ∀ n → (n≡n : n ≡ℕ n) → recover-nat-eq n n n≡n ≡ refl
recover-nat-eq-refl zero   n≡n = refl
recover-nat-eq-refl (1+ n) n≡n = cong (cong suc) (recover-nat-eq-refl n n≡n)

{-# REWRITE recover-nat-eq-refl #-}

record [_≤_][_]₂ (p n δ : ℕ) : Type where
  eta-equality
  constructor ineq₂
  field
    .Hpn : p + δ ≡ℕ n
open [_≤_][_]₂ public

record [_≤_≤_][_]₃ (p q n δ : ℕ) : Type where
  eta-equality
  constructor ineq₃
  field
    δpn δqn : ℕ
    .Hpq  : p + δ ≡ℕ q
    .Hpn  : p + δpn ≡ℕ n
    .Hqn  : q + δqn ≡ℕ n
    .Hpqn : δ + δqn ≡ℕ δpn
open [_≤_≤_][_]₃ public

record [_≤_≤_≤_][_]₄ (p r q n δ : ℕ) : Type where
  eta-equality
  constructor ineq₄
  field
    δpq δpn δrq δrn δqn : ℕ
    .Hpr  : p + δ ≡ℕ r
    .Hpq  : p + δpq ≡ℕ q
    .Hpn  : p + δpn ≡ℕ n
    .Hrq  : r + δrq ≡ℕ q
    .Hrn  : r + δrn ≡ℕ n
    .Hqn  : q + δqn ≡ℕ n
    .Hprq : δ + δrq ≡ℕ δpq
    .Hprn : δ + δrn ≡ℕ δpn
    .Hpqn : δpq + δqn ≡ℕ δpn
    .Hrqn : δrq + δqn ≡ℕ δrn
open [_≤_≤_≤_][_]₄ public

drop₃-1 : ∀ {p q n δ} → (h : [ p ≤ q ≤ n ][ δ ]₃) → [ q ≤ n ][ h .δqn ]₂
drop₃-1 (ineq₃ _ δqn _ _ Hqn _) =
 ineq₂ Hqn

drop₃-2 : ∀ {p q n δ} → (h : [ p ≤ q ≤ n ][ δ ]₃) → [ p ≤ n ][ h .δpn ]₂
drop₃-2 (ineq₃ _ _ _ Hpn _ _) =
 ineq₂ Hpn

drop₄-1 : ∀ {p r q n δ} → (h : [ p ≤ r ≤ q ≤ n ][ δ ]₄) → [ r ≤ q ≤ n ][ h .δrq ]₃
drop₄-1 (ineq₄ _ _ δrq δrn δqn _ _ _ Hrq Hrn Hqn _ _ _ Hrqn) =
 ineq₃ δrn δqn Hrq Hrn Hqn Hrqn

drop₄-2 : ∀ {p r q n δ} → (h : [ p ≤ r ≤ q ≤ n ][ δ ]₄) → [ p ≤ q ≤ n ][ h .δpq ]₃
drop₄-2 (ineq₄ δpq δpn _ _ δqn _ Hpq Hpn _ _ Hqn _ _ Hpqn _) =
 ineq₃ δpn δqn Hpq Hpn Hqn Hpqn

drop₄-3 : ∀ {p r q n δ} → [ p ≤ r ≤ q ≤ n ][ δ ]₄ → [ p ≤ r ≤ n ][ δ ]₃
drop₄-3 (ineq₄ _ δpn _ δrn _ Hpr _ Hpn _ Hrn _ _ Hprn _ _) =
 ineq₃ δpn δrn Hpr Hpn Hrn Hprn

0≤n : ∀ n → [ 0 ≤ n ][ n ]₂
0≤n n = ineq₂ (≡ℕ-refl n)

◆₂_ : ∀ n → [ n ≤ n ][ 0 ]₂
◆₂ n = ineq₂ (≡ℕ-refl n)

◆₃_ : ∀ {p n δ} → [ p ≤ n ][ δ ]₂ → [ p ≤ p ≤ n ][ 0 ]₃
◆₃_ {p} {n} {δ} (ineq₂ Hpn) = ineq₃ δ δ (≡ℕ-refl p) Hpn Hpn (≡ℕ-refl δ)

◆₃'_ : ∀ {p n δ} → [ p ≤ n ][ δ ]₂ → [ p ≤ n ≤ n ][ δ ]₃
◆₃'_ {n = n} {δ} (ineq₂ Hpn) = ineq₃ δ 0 Hpn Hpn (≡ℕ-refl n) (≡ℕ-refl δ)

◆₄_ : ∀ {p q n δ} → [ p ≤ q ≤ n ][ δ ]₃ → [ p ≤ p ≤ q ≤ n ][ 0 ]₄
◆₄_ {p} {δ = δ} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) =
 ineq₄ δ δpn δ δpn δqn (≡ℕ-refl p) Hpq Hpn Hpq Hpn Hqn (≡ℕ-refl δ) (≡ℕ-refl δpn) Hpqn Hpqn

◆₄'_ : ∀ {p q n δ} → [ p ≤ q ≤ n ][ δ ]₃ → [ p ≤ q ≤ n ≤ n ][ δ ]₄
◆₄'_ {n = n} {δ} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) =
 ineq₄ δpn δpn δqn δqn 0 Hpq Hpn Hpn Hqn Hqn (≡ℕ-refl n) Hpqn Hpqn (≡ℕ-refl δpn) (≡ℕ-refl δqn)

↓₂_ : ∀ {p n δ} → [ 1+ p ≤ n ][ δ ]₂ → [ p ≤ n ][ 1+ δ ]₂
↓₂ ineq₂ Hpn = ineq₂ Hpn

⇓₂_ : ∀ {p n δ} → [ 1+ p ≤ 1+ n ][ δ ]₂ → [ p ≤ n ][ δ ]₂
⇓₂ ineq₂ Hpn = ineq₂ Hpn

↑₂_ : ∀ {p n δ} → [ p ≤ n ][ δ ]₂ → [ p ≤ 1+ n ][ 1+ δ ]₂
↑₂ ineq₂ Hpn = ineq₂ Hpn

←₂_ : ∀ {p n δ} → [ p ≤ n ][ 1+ δ ]₂ → [ 1+ p ≤ n ][ δ ]₂
←₂ ineq₂ Hpn = ineq₂ Hpn


⇑₂_ : ∀ {p n δ} → [ p ≤ n ][ δ ]₂ → [ 1+ p ≤ 1+ n ][ δ ]₂
⇑₂ ineq₂ Hpn = ineq₂ Hpn

↓₃_ : ∀ {p q n δ} → [ 1+ p ≤ q ≤ n ][ δ ]₃ → [ p ≤ q ≤ n ][ 1+ δ ]₃
↓₃ ineq₃ δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn

↓₃'_ : ∀ {p q n δ} → [ 1+ p ≤ 1+ q ≤ n ][ δ ]₃ → [ p ≤ q ≤ n ][ δ ]₃
↓₃' ineq₃ δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ (1+ δpn) (1+ δqn) Hpq Hpn Hqn Hpqn

⇓₃_ : ∀ {p q n δ} → [ 1+ p ≤ 1+ q ≤ 1+ n ][ δ ]₃ → [ p ≤ q ≤ n ][ δ ]₃
⇓₃ ineq₃ δpn δqn Hpq Hpn Hqn Hpqn =
 ineq₃ δpn δqn Hpq Hpn Hqn Hpqn
 
↑₃_ : ∀ {p q n δ} → [ p ≤ q ≤ n ][ δ ]₃ → [ p ≤ q ≤ 1+ n ][ δ ]₃
↑₃ ineq₃ δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ (1+ δpn) (1+ δqn) Hpq Hpn Hqn Hpqn

↑₃'_ : ∀ {p q n δ} → [ p ≤ q ≤ n ][ δ ]₃ → [ p ≤ 1+ q ≤ 1+ n ][ 1+ δ ]₃
↑₃' ineq₃ δpn δqn Hpq Hpn Hqn Hpqn =
  ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn

⇑₃_ : ∀ {p q n δ} → [ p ≤ q ≤ n ][ δ ]₃ → [ 1+ p ≤ 1+ q ≤ 1+ n ][ δ ]₃
⇑₃ ineq₃ δpn δqn Hpq Hpn Hqn Hpqn =
 ineq₃ δpn δqn Hpq Hpn Hqn Hpqn
 
↓₄_ : ∀ {p r q n δ} → [ 1+ p ≤ r ≤ q ≤ n ][ δ ]₄ → [ p ≤ r ≤ q ≤ n ][ 1+ δ ]₄
↓₄ ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn =
  ineq₄ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn

⇓₄_ : ∀ {p r q n δ} → [ 1+ p ≤ 1+ r ≤ 1+ q ≤ 1+ n ][ δ ]₄ → [ p ≤ r ≤ q ≤ n ][ δ ]₄ 
⇓₄ ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn =
  ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn

--examples of induction, not usable in practice

variable
  ℓ : Level

≤₂-ind : ∀ p n {δ} (p≤n : [ p ≤ n ][ δ ]₂)
       → (P : ∀ p {δ} → [ p ≤ n ][ δ ]₂ → Type ℓ)
       → (base : P n (◆₂ n))
       → (rec : ∀ p {δ} → (p<n : [ 1+ p ≤ n ][ δ ]₂) → P (1+ p) p<n → P p (↓₂ p<n))
       → P p p≤n
≤₂-ind p n {zero} (ineq₂ Hpn) P base rec with recover-nat-eq p n Hpn
... | refl = base
≤₂-ind p n {1+ δ} (ineq₂ Hpn) P base rec =
  rec p (ineq₂ Hpn) (≤₂-ind (1+ p) n _ P base rec)

≤₃-ind : ∀ p q n {δ} (p≤q≤n : [ p ≤ q ≤ n ][ δ ]₃)
       → (P : ∀ p q {δ} → [ p ≤ q ≤ n ][ δ ]₃ → Type ℓ)
       → (base : ∀ q {δ} (q≤n : [ q ≤ n ][ δ ]₂) → P q q (◆₃ q≤n))
       → (rec : ∀ p q {δ} → (p≤q<n : [ 1+ p ≤ q ≤ n ][ δ ]₃)
                          → P (1+ p) q p≤q<n
                          → P p q (↓₃ p≤q<n))
       → P p q p≤q≤n
≤₃-ind p q n {zero} (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn) P base rec with
  recover-nat-eq p q Hpq | recover-nat-eq δqn δpn Hpqn
... | refl | refl = base p (ineq₂ _)
≤₃-ind p (1+ q) n {1+ δ} (ineq₃ (1+ δpn) δqn Hpq Hpn Hqn Hpqn) P base rec =
  let 1+p≤q≤n = ineq₃ δpn δqn Hpq Hpn Hqn Hpqn in
  rec p (1+ q) 1+p≤q≤n (≤₃-ind (1+ p) (1+ q) n _ P base rec)

≤₄-ind : ∀ p r q n {δ} (p≤r≤q≤n : [ p ≤ r ≤ q ≤ n ][ δ ]₄)
       → (P : ∀ p r q {δ} → [ p ≤ r ≤ q ≤ n ][ δ ]₄ → Type ℓ)
       → (base : ∀ r q {δ} (r≤q≤n : [ r ≤ q ≤ n ][ δ ]₃) → P r r q (◆₄ r≤q≤n))
       → (rec : ∀ p r q {δ}
              → (p≤r≤q<n : [ 1+ p ≤ r ≤ q ≤ n ][ δ ]₄)
              → P (1+ p) r q p≤r≤q<n
              → P p r q (↓₄ p≤r≤q<n))
       → P p r q p≤r≤q≤n
≤₄-ind p r q n {zero} (ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn)  P base rec
  with recover-nat-eq p r Hpr | recover-nat-eq δrq δpq Hprq | recover-nat-eq δrn δpn Hprn
... | refl | refl | refl = base p q (ineq₃ δpn δqn Hpq Hpn Hqn Hpqn)
≤₄-ind p (1+ r) (1+ q) n {1+ δ} (ineq₄ (1+ δpq) (1+ δpn) δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn) P base rec =
  let 1+p≤r≤q≤n = ineq₄ δpq δpn δrq δrn δqn Hpr Hpq Hpn Hrq Hrn Hqn Hprq Hprn Hpqn Hrqn in
  rec p (1+ r) (1+ q) 1+p≤r≤q≤n (≤₄-ind (1+ p) (1+ r) (1+ q) n _ P base rec)
