open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module νSet
  (fe : FunExt-Axiom)
  (ua : Univalence-Axiom)  
  (arity : Type)
  where

open import νSet.Base fe arity public
open import νSet.Face fe arity public
open import νSet.Bisim fe ua arity public
