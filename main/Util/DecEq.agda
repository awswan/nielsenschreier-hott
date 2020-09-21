{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Sigma

{- Some miscellaneous lemmas for types with decidable equality. -}
module Util.DecEq where

×-has-dec-eq : {i j : ULevel} {A : Type i} {B : Type j} → (has-dec-eq A) → (has-dec-eq B) →
  (has-dec-eq (A × B))

×-has-dec-eq Adec Bdec (a , b) (a' , b') =
  ⊔-rec (⊔-rec (λ p q → inl (pair×= q p)) (λ f _ → inr (λ p → f (ap snd p))) (Bdec b b'))
        (λ f → inr (λ p → f (ap fst p))) (Adec a a')

equiv-preserves-dec-eq : {i j : ULevel} {A : Type i} {B : Type j} → (A ≃ B) → (has-dec-eq B) →
  has-dec-eq A

equiv-preserves-dec-eq e Adec a a' = ⊔-rec (λ p → inl (–>-is-inj e a a' p))
  (λ f → inr (λ p → f (ap (–> e) p))) (Adec (–> e a) (–> e a'))

