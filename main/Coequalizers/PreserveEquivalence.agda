{-# OPTIONS --without-K --rewriting --exact-split #-}

open import lib.Basics
open import lib.types.PushoutFmap
open import lib.types.Span
open import lib.types.Coproduct
open import lib.types.Paths

open import Graphs.Definition
open import Coequalizers.Definition
open import Util.Coproducts

{- We show that given equivalences E ≃ E' and V ≃ V' that commute with endpoint maps
   we get an equivalence between coequalizers V / E ≃ V' / E'. This could have been
   derived from the corresponding result for pushouts in the HoTT-Agda library, but
   for reference we give the proof using univalence appearing in the paper.
-}  
module Coequalizers.PreserveEquivalence where

Coeq-preserves-= : {i j : ULevel} (V : Type i) (E : Type j) (π₀ π₁ : E → V)
  (V' : Type i) (E' : Type j) (π₀' π₁' : E' → V')
  (eV : V == V') (eE : E == E') (comm₀ : coe eV ∘ π₀ == π₀' ∘ coe eE ) (comm₁ : coe eV ∘ π₁ == π₁' ∘ coe eE) →
  (Coeq (graph π₀ π₁) ≃ Coeq (graph π₀' π₁'))

Coeq-preserves-= V E π₀ π₁ .V .E .(λ x → π₀ x) .(λ x → π₁ x) idp idp idp idp = ide _


{- The easiest version of the lemma assumes that V has the same universe level as V'
   and E has the same universe level as E'. -}
Coeq-emap-same-level : {i j : ULevel} {V : Type i} {E : Type j} ⦃ gph : Graph E V ⦄
  {V' : Type i} {E' : Type j} ⦃ gph' : Graph E' V' ⦄
  (eV : V ≃ V') (eE : E ≃ E')
  (comm₀ : –> eV ∘ π₀ ∼ π₀ ∘ –> eE )
  (comm₁ : –> eV ∘ π₁ ∼ π₁ ∘ –> eE ) → (Coeq gph ≃ Coeq gph')

Coeq-emap-same-level eV eE comm₀ comm₁ = Coeq-preserves-= _ _ π₀ π₁ _ _ π₀ π₁ (ua eV) (ua eE)
  (λ= (λ e → coe-β eV _ ∙ comm₀ e ∙ ap π₀ (! (coe-β eE e))))
  (λ= (λ e → coe-β eV _ ∙ comm₁ e ∙ ap π₁ (! (coe-β eE e))))
                                                       

{- We now deal with the case where all the types can have different universe levels.
   We first show that every coequalizer is equivalent to its lift to higher universe
   levels. -}
module LiftGraph {i j : ULevel} (V : Type i) (E : Type j) ⦃ gph : Graph E V ⦄ (i' j' : ULevel) where
  instance
    lift-graph : Graph (Lift {j = j'} E) (Lift {j = i'} V)
    lift-graph = graph (λ { (lift e) → lift (π₀ e)}) λ { (lift e) → lift (π₁ e)}

  Coeq-Lift-≃ : Coeq gph ≃ Coeq (lift-graph)
  Coeq-Lift-≃ = equiv f g f-g g-f
    where
      f : V / E → (Lift V) / (Lift E)
      f = Coeq-rec (c[_] ∘ lift) (λ e → quot (lift e))

      g : (Lift V) / (Lift E) → V / E
      g = Coeq-rec (λ {(lift v) → c[ v ]}) (λ {(lift e) → quot e})

      g-f : (z : V / E) → (g (f z) == z)
      g-f = Coeq-elim _ (λ v → idp) (λ e → ↓-app=idf-in (! (p e)))
        where
          p : (e : E) → ap (g ∘ f) (quot e) ∙ idp == idp ∙' (quot e)
          p e =
            ap (g ∘ f) (quot e) ∙ idp
              =⟨ ∙-unit-r _ ⟩
            ap (g ∘ f) (quot e)
              =⟨ ap-∘ g f (quot e) ⟩
            ap g (ap f (quot e))
              =⟨ ap (ap g) (Coeq-rec-β= _ _ e) ⟩
            ap g (quot (lift e))
              =⟨ Coeq-rec-β= _ _ (lift e) ⟩
            quot e
              =⟨ ! (∙'-unit-l _) ⟩            
            idp ∙' (quot e)
              =∎

      f-g : (z : (Lift V) / (Lift E)) → (f (g z) == z)
      f-g = Coeq-elim _ (λ v → idp) (λ {(lift e) → ↓-app=idf-in (! (p e))})
        where
          p : (e : E) → ap (f ∘ g) (quot (lift e)) ∙ idp == idp ∙' quot (lift e)
          p e = 
            ap (f ∘ g) (quot (lift e)) ∙ idp
              =⟨ ∙-unit-r _ ⟩
            ap (f ∘ g) (quot (lift e))
              =⟨ ap-∘ f g _ ⟩
            ap f (ap g (quot (lift e)))
              =⟨ ap (ap f) (Coeq-rec-β= _ _ _) ⟩
            ap f (quot e)
              =⟨ Coeq-rec-β= _ _ _ ⟩
            quot (lift e)
              =⟨ ! (∙'-unit-l _) ⟩
            idp ∙' quot (lift e)
              =∎

{- We can now derive that coequalizers preserve equivalences where
   the types can have different universe levels. -}
Coeq-emap : {i j i' j' : ULevel} {V : Type i} {E : Type j} ⦃ gph : Graph E V ⦄
  {V' : Type i'} {E' : Type j'} ⦃ gph' : Graph E' V' ⦄ → 
  (eV : V ≃ V') (eE : E ≃ E')
  (comm₀ : –> eV ∘ π₀ ∼ π₀ ∘ –> eE )
  (comm₁ : –> eV ∘ π₁ ∼ π₁ ∘ –> eE ) → (Coeq gph ≃ Coeq gph')

Coeq-emap {i} {j} {i'} {j'} {V} {E} ⦃ gph ⦄ {V'} {E'} ⦃ gph' ⦄ eV eE comm₀ comm₁ =
  V / E
    ≃⟨ LEV.Coeq-Lift-≃ ⟩
  Lift V / Lift E
    ≃⟨ Coeq-emap-same-level
       (lower-equiv ⁻¹ ∘e eV ∘e lower-equiv)
       (lower-equiv ⁻¹ ∘e eE ∘e lower-equiv)
       (λ {(lift e) → ap lift (comm₀ e)})
       (λ {(lift e) → ap lift (comm₁ e)}) ⟩
  Lift V' / Lift E'
    ≃⟨ LEV'.Coeq-Lift-≃ ⁻¹ ⟩
  V' / E'
    ≃∎
  where
    module LEV = LiftGraph V E i' j'
    module LEV' = LiftGraph V' E' i j
