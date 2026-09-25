open import Prelude
open import Equiv

open import Axioms.FunExt
open import Axioms.Univalence

open import HSet.Base

import HSet.FunExt as HSet-FE

module HSet.UA
 (fe-axiom : FunExt-Axiom)
 (ua-axiom : Univalence-Axiom)
 where

 open HSet-FE fe-axiom
 open UA ua-axiom

 HSet-≃ : (A B : HSet) → A .Dom ≃ B .Dom → A ≡ B
 HSet-≃ A B = HSet-≡ A B ∘ ua 
 
