open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module Presheaf
  (fe : FunExt-Axiom)
  (ua : Univalence-Axiom)  
  (arity : Type)
  where

open import Presheaf.Base arity public
open import Presheaf.Zipper arity public

open Presheaf-UA fe ua public
