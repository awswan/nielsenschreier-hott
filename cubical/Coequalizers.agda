{-# OPTIONS --cubical --without-K #-}

open import Cubical.Core.Everything
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sum
open import Cubical.Data.Unit

module Coequalizers where

record Graph {ℓ ℓ' : Level} (E : Type ℓ) (V : Type ℓ') : Type (ℓ-max ℓ ℓ') where
  field
    π₀ : E → V
    π₁ : E → V

open Graph ⦃...⦄

data Coeq {ℓ ℓ' : Level} {V : Type ℓ} {E : Type ℓ'} (ev : Graph E V) :
          Type (ℓ-max ℓ ℓ')  where
  c[_] : V → (Coeq ev)
  quot : (e : E) → c[ (Graph.π₀ ev e) ] ≡ c[ (Graph.π₁ ev e) ]

_/_ : {ℓ ℓ' : Level} (V : Type ℓ) (E : Type ℓ') ⦃ ev : Graph E V ⦄ →
         Type (ℓ-max ℓ ℓ')
_/_ V E ⦃ ev ⦄ = Coeq ev

infix 25 _/_


module CoprodCoeq {ℓ ℓ' ℓ'' : Level} (E₀ : Type ℓ) (E₁ : Type ℓ') (V : Type ℓ'')
  ⦃ ev : Graph (E₀ ⊎ E₁) V ⦄ where
  instance
    evE₀ : Graph E₀ V
    evE₀ = record { π₀ = π₀ ∘ inl ; π₁ = π₁ ∘ inl }

    ev-snd : Graph E₁ (V / E₀)
    ev-snd = record { π₀ = c[_] ∘ π₀ ∘ inr ; π₁ = c[_] ∘ π₁ ∘ inr }

  coeq-coprod-equiv : V / (E₀ ⊎ E₁) ≃ (V / E₀) / E₁
  coeq-coprod-equiv = isoToEquiv (iso f g f-g g-f)
    where
      f : V / (E₀ ⊎ E₁) → (V / E₀) / E₁
      f c[ x ] = c[ c[ x ] ]
      f (quot (inl e) i) = c[ quot e i ]
      f (quot (inr e) i) = quot e i

      g : (V / E₀) / E₁ →  V / (E₀ ⊎ E₁)
      g c[ c[ x ] ] = c[ x ]
      g c[ quot e i ] = quot (inl e) i
      g (quot e i) = quot (inr e) i

      f-g : (z : (V / E₀) / E₁) → (f (g z) ≡ z)
      f-g c[ c[ x ] ] = refl
      f-g c[ quot e i ] = refl
      f-g (quot e i) = refl

      g-f : (z : V / (E₀ ⊎ E₁)) → (g (f z) ≡ z)
      g-f c[ x ] = refl
      g-f (quot (inl e) i) = refl
      g-f (quot (inr e) i) = refl


module TrivialExtension {ℓ ℓ' : Level} (V : Type ℓ) (v : V) where
  instance
    evt-l : Graph Unit (V ⊎ Unit)
    evt-l = record { π₀ = λ x → inl v ; π₁ = inr }

    evt-r : Graph Unit (Unit ⊎ V)
    evt-r = record { π₀ = inl ; π₁ = λ _ → inr v }

  te-equiv-l : V ≃ (V ⊎ Unit) / Unit
  te-equiv-l = isoToEquiv (iso (c[_] ∘ inl) g f-g (λ _ → refl))
    where
      g : (V ⊎ Unit) / Unit → V
      g c[ inl x ] = x
      g c[ inr x ] = v
      g (quot e i) = v

      f-g : (z : (V ⊎ Unit) / Unit) → c[ inl (g z) ] ≡ z
      f-g c[ inl x ] = refl
      f-g c[ inr x ] = quot x
      f-g (quot e i) j = quot e (i ∧ j)

  te-equiv-r : V ≃ (Unit ⊎ V) / Unit
  te-equiv-r = isoToEquiv (iso (c[_] ∘ inr) g f-g λ _ → refl)
    where
      g : (Unit ⊎ V) / Unit → V
      g c[ inl x ] = v
      g c[ inr x ] = x
      g (quot e i) = v

      f-g : (z : (Unit ⊎ V) / Unit) → c[ inr (g z) ] ≡ z
      f-g c[ inl x ] i = quot x (~ i)
      f-g c[ inr x ] = refl
      f-g (quot e i) j = quot e (i ∨ ~ j)
