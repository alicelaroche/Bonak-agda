open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module νSet
  (arity : ℕ)
  where

open import νSet.Context public

open import νSet.Frame arity public
open import νSet.Painting arity public
open import νSet.Restr-Frame arity public
open import νSet.Restr-Painting arity public
open import νSet.Coh-Frame arity public
open import νSet.Coh-Painting arity public
