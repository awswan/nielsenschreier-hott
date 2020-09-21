{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.Function2
open import lib.NType2

open import Graphs.Definition
open import Coequalizers.Definition

open import Util.Misc

module Coequalizers.Misc where

module _ {i j : ULevel} {E : Type i} {V : Type j} ⦃ gph : Graph E V ⦄ where
  inh-coeq-to-vertex : ∥ V / E ∥ → ∥ V ∥
  inh-coeq-to-vertex = Trunc-rec (Coeq-rec [_] (λ _ → prop-has-all-paths _ _))

  quotient-map-is-surj : is-surj (c[_] :> (V → V / E))
  quotient-map-is-surj = Coeq-elim (λ v → ∥ hfiber c[_] v ∥) (λ v → [ v , idp ]) λ _ → prop-has-all-paths-↓
