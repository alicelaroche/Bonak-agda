open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module Correspondence
  (fe : FunExt-Axiom)
  (ua : Univalence-Axiom)  
  (arity : Type)
  where

open import Correspondence.PresheafToνSet fe ua arity public
open import Correspondence.νSetToPresheaf fe ua arity public
open import Correspondence.Inverses fe ua arity public
