{-# OPTIONS --without-K --rewriting --exact-split #-}

open import lib.Basics
open import lib.types.Paths
open import lib.types.Coproduct

open import Graphs.Definition

open import Coequalizers.Definition

module Coequalizers.TrivialExtension where

module TExtensionCoeq-l {i : ULevel} {V : Type i} (v : V) where
  instance
    tegph : Graph ⊤ (V ⊔ ⊤)
    tegph = record { π₀ = λ _ → inl v ; π₁ = λ _ → inr unit }

  extn-equiv : V ≃ ((V ⊔ ⊤) / ⊤)
  extn-equiv = equiv ((c[_] ∘ inl)) (((Coeq-rec (⊔-rec (idf V) (λ _ → v)) λ e → idp))) ((Coeq-elim _ (λ { (inl v') → idp ; (inr x) → quot x}) λ {unit → ↓-app=idf-in (∙'-unit-l _ ∙ ! lem ∙ᵣ quot unit)}))
                      λ _ → idp
    where
      lem : ap (c[_] ∘ inl ∘ (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp ))) (quot unit) == idp
      lem =
        ap (c[_] ∘ inl ∘ (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp ))) (quot unit)
          =⟨ ap-∘ (c[_] ∘ inl) (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp )) (quot unit) ⟩
        ap (c[_] ∘ inl) (ap (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp )) (quot unit))
          =⟨ ap (ap (c[_] ∘ inl)) (Coeq-rec-β= _ _ _) ⟩
        ap (c[_] ∘ inl)  idp
          =⟨ idp ⟩
        idp
          =∎

module TExtensionCoeq-r {i : ULevel} {V : Type i} (v : V) where
  instance
    tegph : Graph ⊤ (V ⊔ ⊤)
    tegph = record { π₀ = λ _ → inr unit ; π₁ = λ _ → inl v }

  extn-equiv : V ≃ ((V ⊔ ⊤) / ⊤)
  extn-equiv = equiv ((c[_] ∘ inl)) (((Coeq-rec (⊔-rec (idf V) (λ _ → v)) λ e → idp))) ((Coeq-elim _ (λ { (inl v') → idp ; (inr x) → ! (quot x)}) λ {unit → ↓-app=idf-in ((!-inv'-l (quot unit) ∙ ! lem ∙ ! (∙-unit-r _)))}))
                      λ _ → idp
    where
      lem : ap (c[_] ∘ inl ∘ (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp ))) (quot unit) == idp
      lem =
        ap (c[_] ∘ inl ∘ (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp ))) (quot unit)
          =⟨ ap-∘ (c[_] ∘ inl) (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp )) (quot unit) ⟩
        ap (c[_] ∘ inl) (ap (Coeq-rec (⊔-rec (λ x → x) (λ _ → v)) (λ e → idp )) (quot unit))
          =⟨ ap (ap (c[_] ∘ inl)) (Coeq-rec-β= _ _ _) ⟩
        ap (c[_] ∘ inl)  idp
          =⟨ idp ⟩
        idp
          =∎
