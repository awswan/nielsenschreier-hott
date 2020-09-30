{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.types.Truncation

open import Coequalizers.Definition
open import Coequalizers.Misc

open import Graphs.Definition

open import Util.Misc

module Groups.Definition where

{- BG has the structure of a type theoretic group if it is pointed, connected and
   1-truncated.
-} 
record TTGroup {i : ULevel} (BG : Type i) : Type i where
  field
    base : BG
    ⦃ gp-conn ⦄ : is-connected 0 BG
    ⦃ gp-trunc ⦄ : is-gpd BG

open TTGroup ⦃...⦄ public

{- Some functions related to free higher groups (which we never define explicitly). -}
module _ {i : ULevel} {A : Type i} where
  instance -- Whenever we need a pair of maps A ⇉ 1 they are defined as follows
    gph-fhg : Graph A Unit
    gph-fhg = record { π₀ = λ _ → unit ; π₁ = λ _ → unit }

    conn-fhg : is-connected 0 (⊤ / A)
    conn-fhg = has-level-in ([ c[ unit ] ] , Trunc-elim (λ x → Trunc-rec (λ { (t , p) → ap [_] p}) (quotient-map-is-surj x)))

  fhg-base : ⊤ / A
  fhg-base = c[ unit ]

{- The definition of a free group. -}
FreeGroup : {i : ULevel} (A : Type i) → Type i
FreeGroup A = ∥ ⊤ / A ∥₁

instance -- free groups are groups
  free-gp-str : {i : ULevel} {A : Type i} → TTGroup (FreeGroup A)
  free-gp-str = record { base = [ fhg-base ] }

