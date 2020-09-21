{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Paths

open import Graphs.Definition
open import Coequalizers.Definition
open import Util.Misc

module Coequalizers.PullbackStability where

module PullbackStability {i k j : ULevel} (E : Type i) (V : Type k) ⦃ gph : Graph E V ⦄
  (X : (V / E) → Type j) where
  
  VX = Σ V (X ∘ c[_])
  EX = Σ E (X ∘ c[_] ∘ π₀)

  instance
    gph-pb : Graph EX VX
    gph-pb = record { π₀ = λ {(e , x) → ((π₀ e) , x)} ; π₁ = λ {(e , x) → ((π₁ e) , (transport X (quot e) x))} }

  pb-equiv : (VX / EX) ≃ Σ (V / E) X
  pb-equiv = equiv f g (λ {(e , x) → f-g' e x}) g-f
    where

      f-point : VX → Σ (V / E) X
      f-point (v , x) = (c[ v ] , x)

      f : (VX / EX) → Σ (V / E) X
      f = Coeq-rec f-point
               λ {(e , x) → pair= (quot e) (transp-↓' X (quot e) x)}

      g'-path : (e : E) → (λ x → c[ (π₀ e , x) ]) == (λ x → c[ (π₁ e , x) ]) [ (λ z → X z → VX / EX) ↓ (quot e) ]
      g'-path e = ↓-app→cst-in (λ {t} {t'} q → quot (e , t) ∙ ap c[_] (pair= idp (to-transp q)))

      g'-point : (v : V) → (X c[ v ]) → (VX / EX)
      g'-point v x = c[ v , x ]

      g' : (z : V / E) → (X z) → (VX / EX)
      g' = Coeq-elim (λ z → (X z) → (VX / EX))
                     g'-point g'-path


      g : Σ (V / E) X → (VX / EX)
      g (z , x) = g' z x

      g-f : (z : VX / EX) → (g (f z) == z)
      g-f = Coeq-elim _ (λ _ → idp) λ {(e , x) → ↓-app=idf-in (lemma e x)}
        where
          lemma1 : {z z' : V / E} (p : z == z') (x : X z) → ap g (pair= p (transp-↓' X p x)) == ↓-app→cst-out (apd g' p) (transp-↓' X p x)
          lemma1 idp x = idp

          lemma2 : {z z' : V / E} (p : z == z') (x : X z) → (to-transp ((transp-↓' X p x))) == idp
          lemma2 idp x = idp

          lemma : (e : E) → (x : X c[ π₀ e ]) → idp ∙' quot (e , x) == ap (g ∘ f) (quot (e , x)) ∙ idp
          lemma e x = ! $
            ap (g ∘ f) (quot (e , x)) ∙ idp
              =⟨ ∙-unit-r _ ⟩
            ap (g ∘ f) (quot (e , x))
              =⟨ ap-∘ g f (quot (e , x)) ⟩
            ap g (ap f (quot (e , x)))
              =⟨ ap (ap g) (Coeq-rec-β= _ _ _) ⟩
            ap g (pair= (quot e) (transp-↓' X (quot e) x))
              =⟨ lemma1 (quot e) x ⟩
            ↓-app→cst-out (apd g' (quot e)) (transp-↓' X (quot e) x)
              =⟨ ap (λ w → ↓-app→cst-out w (transp-↓' X (quot e) x) ) (Coeq-β= _ _ _ _) ⟩
            ↓-app→cst-out (↓-app→cst-in λ q → quot (e , _) ∙ ap c[_] (pair= idp (to-transp q))) (transp-↓' X (quot e) x)
              =⟨ ↓-app→cst-β ((λ q → quot (e , _) ∙ ap c[_] (pair= idp (to-transp q)))) ((transp-↓' X (quot e) x)) ⟩
            (λ q → quot (e , _) ∙ ap c[_] (pair= idp (to-transp q))) (transp-↓' X (quot e) x)
              =⟨ idp ⟩
            quot (e , _) ∙ ap c[_] (pair= idp (to-transp ((transp-↓' X (quot e) x))))
              =⟨ quot (e , x) ∙ₗ ap (ap c[_]) (pair== idp (lemma2 (quot e) x)) ⟩
            quot (e , x) ∙ idp
              =⟨ ∙-unit-r _ ⟩
            quot (e , x)
              =⟨ ! (∙'-unit-l _) ⟩
            idp ∙' quot (e , x)
              =∎

      f-g' : (z : V / E) → (x : X z) → f (g' z x) == (z , x)
      f-g' = Coeq-elim (λ z → (x : X z) → f (g' z x) == (z , x) )
                       (λ v x → idp) λ e → lemma1 (quot e) (λ _ → idp) (λ _ → idp) (λ x → (lemma2 (e , x)))
           where
             fg : (z : V / E) → (x : X z) → Σ (V / E) X
             fg z x = f (g' z x)

             lemma1 : {z z' : V / E} (p : z == z') (α : (x : X z) → f (g' z x) == (z , x))
                            (β : (x' : X z') → f (g' z' x') == (z' , x')) →
                            ((x : X z) → ((α x) ∙ Σ-transp X p x) == (↓-app→cst-out (apd fg p) (transp-↓' _ p x) ∙ (β (transport X p x)))) →
                            α == β [ (λ z'' → (x : X z'') → f (g' z'' x) == (z'' , x)) ↓ p ]

             lemma1 idp α β q = λ= (λ x → ! (∙-unit-r _) ∙ q x)

             expandapd : {z z' : V / E} (p : z == z') {x : X z} {x' : X z'} (q : x == x' [ X ↓ p ]) → ↓-app→cst-out (apd fg p) q == ap f (↓-app→cst-out (apd g' p) q)
             expandapd idp idp = idp


             lemma2 : (ex : EX) →
                          (idp ∙ Σ-transp X (quot (fst ex)) (snd ex)) == (↓-app→cst-out (apd fg (quot (fst ex))) (transp-↓' _ (quot (fst ex)) (snd ex)) ∙ idp)
             lemma2 ex@(e , x) = ! $
               ↓-app→cst-out (apd fg (quot e)) (transp-↓' _ (quot e) x) ∙ idp
                 =⟨ ∙-unit-r _ ⟩
               ↓-app→cst-out (apd fg (quot e)) (transp-↓' _ (quot e) x)
                 =⟨ expandapd (quot e) ((transp-↓' _ (quot e) x)) ⟩
               ap f (↓-app→cst-out (apd g' (quot e)) ((transp-↓' _ (quot e) x)))
                 =⟨ ap (λ w → ap f (↓-app→cst-out w (((transp-↓' _ (quot e) x))))) (Coeq-β= ((λ z → (X z) → (VX / EX))) (λ v x → c[ v , x ]) g'-path e) ⟩
               ap f (↓-app→cst-out (g'-path e) (transp-↓' _ (quot e) x))
                 =⟨ ap (ap f) (↓-app→cst-β ((λ {t} {t'} q → quot (e , t) ∙ ap c[_] (pair= idp (to-transp q)))) ((transp-↓' _ (quot e) x))) ⟩
               ap f (quot ex ∙ ap c[_] (pair= idp (to-transp (transp-↓' X (quot e) x))))
                 =⟨ ap-∙ f (quot ex) (ap c[_] (pair= idp (to-transp (transp-↓' X (quot e) x)))) ⟩
               ap f (quot ex) ∙ ap f (ap c[_] (pair= idp (to-transp (transp-↓' X (quot e) x))))
                 =⟨ ap f (quot ex) ∙ₗ ∘-ap f c[_] _ ⟩
               ap f (quot ex) ∙ ap (f ∘ c[_]) (pair= idp (to-transp (transp-↓' X (quot e) x)))
                 =⟨ idp ⟩
               ap f (quot ex) ∙ ap f-point (pair= idp (to-transp (transp-↓' X (quot e) x)))
                 =⟨ Coeq-rec-β= _ _ _ ∙ᵣ ap f-point (pair= idp (to-transp (transp-↓' X (quot e) x))) ⟩
               pair= (quot e) (transp-↓' X (quot e) x) ∙ ap f-point (pair= idp (to-transp (transp-↓' X (quot e) x)))
                 =⟨ ap (λ w → pair= (quot e) (transp-↓' X (quot e) x) ∙ ap f-point (pair= idp w)) (lemma2a (quot e) x) ⟩
               pair= (quot e) (transp-↓' X (quot e) x) ∙ ap f-point (pair= idp idp)
                 =⟨ ∙-unit-r _ ⟩
               pair= (quot e) (transp-↓' X (quot e) x)
                 =⟨ idp ⟩
               Σ-transp X (quot e) x
                 =⟨ idp ⟩
               idp ∙ Σ-transp X (quot e) x
                 =∎
               where
                 lemma2a : {z z' : V / E} (p : z == z') (x : X z) → (to-transp (transp-↓' X p x)) == idp
                 lemma2a idp x = idp

