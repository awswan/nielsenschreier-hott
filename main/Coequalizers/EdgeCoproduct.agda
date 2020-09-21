{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Coequalizers.Definition

open import lib.Basics
open import lib.types.Paths

open import Graphs.Definition

module Coequalizers.EdgeCoproduct where

module CoeqCoprodEquiv {i j k : ULevel} (V : Type i) (E₁ : Type j) (E₂ : Type k) ⦃ gph : Graph (E₁ ⊔ E₂) V ⦄ where

  instance
    gph1 : Graph E₁ V
    gph1 = record { π₀ = (Graph.π₀ gph) ∘ inl ; π₁ = (Graph.π₁ gph) ∘ inl }

  instance
    gph2 : Graph E₂ (V / E₁)
    gph2 = record { π₀ = c[_] ∘ (Graph.π₀ gph) ∘ inr ; π₁ = c[_] ∘ (Graph.π₁ gph) ∘ inr }
    
  edge-coproduct-expand : (V / (E₁ ⊔ E₂)) ≃ ((V / E₁) / E₂)
  edge-coproduct-expand = equiv f g f-g g-f
    where
      f : V / (E₁ ⊔ E₂) → (V / E₁) / E₂
      f = Coeq-rec (c[_] ∘ c[_]) λ { (inl x) → ap c[_] (quot x) ; (inr x) → quot x}
  
      g : (V / E₁) / E₂ → V / (E₁ ⊔ E₂)
      g = Coeq-rec (Coeq-rec c[_] (λ e → quot (inl e))) (λ e → quot (inr e))

      f-g : (x : (V / E₁) / E₂) → (f (g x) == x)
      f-g = Coeq-elim (λ x' → f (g x') == x') (Coeq-elim (λ x' → f (g (c[ x' ])) == c[ x' ]) (λ v → idp) (λ e → ↓-='-in (lemma1 e))) λ e → ↓-app=idf-in $
        idp ∙' quot e
          =⟨ ∙'-unit-l _ ⟩
        quot e
          =⟨ ! (Coeq-rec-β= _ _ _) ⟩
        ap f (quot (inr e))
          =⟨ ap (ap f) (! (Coeq-rec-β= _ _ _)) ⟩
        ap f (ap g (quot e))
          =⟨ ! (ap-∘ f g (quot e)) ⟩
        ap (f ∘ g) (quot e)
          =⟨ ! (∙-unit-r _) ⟩
        ap (f ∘ g) (quot e) ∙ idp
          =∎
        where
          lemma1 : (e : E₁) → idp ∙' ap (λ z → c[ z ]) (quot e) ==
                      ap (λ z → f (g c[ z ])) (quot e) ∙ idp
          lemma1 e =
            idp ∙' ap c[_] (quot e)
              =⟨ ∙'-unit-l _ ⟩
            ap c[_] (quot e)
              =⟨ ! (Coeq-rec-β= _ _ _) ⟩
            ap f (quot (inl e))
              =⟨ ap (ap f) (! (Coeq-rec-β= _ _ _)) ⟩
            ap f (ap (Coeq-rec c[_] (λ e → quot (inl e))) (quot e))
              =⟨ idp ⟩
            ap f (ap (g ∘ c[_]) (quot e))
              =⟨ ! (ap-∘ f (g ∘ c[_]) (quot e)) ⟩
            ap (f ∘ g ∘ c[_]) (quot e)
              =⟨ ! (∙-unit-r _) ⟩
            ap (f ∘ g ∘ c[_]) (quot e) ∙ idp
              =∎


      g-f : (x : V / (E₁ ⊔ E₂)) → (g (f x) == x)
      g-f = Coeq-elim (λ x → g (f x) == x) (λ v → idp) (λ { (inl e) → ↓-app=idf-in (! (lemma1 e)) ; (inr e) → ↓-app=idf-in (! (lemma2 e))})
        where
          lemma1 : (e : E₁) → ap (λ z → g (f z)) (quot (inl e)) ∙ idp == idp ∙' quot (inl e)
          lemma1 e =
            ap (g ∘ f) (quot (inl e)) ∙ idp
              =⟨ ∙-unit-r _ ⟩
            ap (g ∘ f) (quot (inl e))
               =⟨ ap-∘ g f (quot (inl e)) ⟩
            ap g (ap f (quot (inl e)))
              =⟨ ap (ap g) (Coeq-rec-β= _ _ _) ⟩
            ap g (ap c[_] (quot e))
              =⟨ ! (ap-∘ g c[_] (quot e)) ⟩
            ap (g ∘ c[_]) (quot e)
              =⟨ idp ⟩
            ap (Coeq-rec c[_] (λ e' → quot (inl e'))) (quot e)
              =⟨ Coeq-rec-β= _ _ _ ⟩
            quot (inl e)
              =⟨ ! (∙'-unit-l _) ⟩
            idp ∙' quot (inl e)
              =∎

          lemma2 : (e : E₂) → ap (λ z → g (f z)) (quot (inr e)) ∙ idp == idp ∙' quot (inr e)
          lemma2 e =
            ap (g ∘ f) (quot (inr e)) ∙ idp
              =⟨ ∙-unit-r _ ⟩
            ap (g ∘ f) (quot (inr e))
              =⟨ ap-∘ g f (quot (inr e)) ⟩
            ap g (ap f (quot (inr e)))
              =⟨ ap (ap g) (Coeq-rec-β= _ _ _) ⟩
            ap g (quot e)
              =⟨ Coeq-rec-β= _ _ _ ⟩
            quot (inr e)
              =⟨ ! (∙'-unit-l _) ⟩
            idp ∙' quot (inr e)
              =∎

