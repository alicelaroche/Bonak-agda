open import Prelude
open import Axioms.FunExt
open import Axioms.Univalence

module νSet
  (fe : FunExt-Axiom)
  (ua : Univalence-Axiom)  
  (arity : Type)
  where

open import νSet.Base fe arity using
  ( Ctx; fullframe; []; _∷_; TotalSpace
  ; νSet->; this; next; νSet) public
open import νSet.Face fe arity using (νFace; νFace-coh; νFace-≡) public
open import νSet.Bisim fe ua arity public
