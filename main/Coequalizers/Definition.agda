{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Basics
open import lib.PathOver
open import lib.PathGroupoid
open import lib.types.Pushout
open import lib.types.Span
open import lib.types.Coproduct
open import lib.types.Sigma

open import Graphs.Definition hiding (π₀ ; π₁)

open import Util.Misc

module Coequalizers.Definition where

Coeq : ∀ {i j} {E : Type i} {V : Type j} → (Graph E V) → Type (lmax i j)
Coeq {E = E} {V = V} (graph π₀ π₁) = Pushout (span V V (V ⊔ E) (⊔-rec (idf V) π₀) (⊔-rec (idf V) π₁))


  
{- It's often clearer to write coequalizers as V / E, where V and E are the 
   vertex and egde types, ommiting the endpoint maps. We implement this idea in
   agda using instance arguments.
-}
module _ {i j : ULevel} where
  _/_ : (V : Type j) (E : Type i) ⦃ gph : Graph E V ⦄ → Type (lmax i j)
  _/_ V E ⦃ gph ⦄ = Coeq gph


  infix 80 _/_


module _ {i j : ULevel} {V : Type i} {E : Type j} {gph : Graph E V} where
  open Graph gph
  
  cspan : Span
  cspan = span V V (V ⊔ E) (⊔-rec (idf V) π₀) (⊔-rec (idf V) π₁)

  c[_] : V → Coeq gph
  c[ v ] = left v

  quot : (e : E) → c[ π₀ e ] == c[ π₁ e ]
  quot e = glue (inr e) ∙ ! (glue (inl (π₁ e)))

  private
    lemma : {j : ULevel} {X : Coeq gph → Type j} {a b c : Coeq gph} (p : a == b) (q : c == b) {x : X a} {y : X b} {z : X c} → (x == z [ X ↓ (p ∙ ! q) ]) →
            (z == y [ X ↓ q ]) → (x == y [ X ↓ p ])
    lemma idp idp r s = r ∙ s

  module _ {j : ULevel} (X : Coeq gph → Type j) (x : (v : V) → X c[ v ])
    (p : (e : E) → x (π₀ e) == x (π₁ e) [ X ↓ quot e ]) where

    Coeq-elim : (z : Coeq gph) → X z
    Coeq-elim = Pushout-elim x (λ v → transport X (glue (inl v)) (x v)) λ {(inl v) → transp-↓' _ _ _ ; (inr e) → lemma _ _ (p e) (transp-↓' _ _ _)}

    Coeq-β= : (e : E) → apd Coeq-elim (quot e) == p e
    Coeq-β= e =
      apd Coeq-elim (quot e)
        =⟨ apd-∙ Coeq-elim (glue (inr e)) (! (glue (inl (π₁ e)))) ⟩
      apd Coeq-elim (glue (inr e)) ∙ᵈ apd Coeq-elim (! (glue (inl (π₁ e))))
        =⟨ PushoutElim.glue-β _ _ _ _ ∙ᵈᵣ apd Coeq-elim (! (glue (inl (π₁ e)))) ⟩
      lemma _ _ (p e) (transp-↓' _ _ _) ∙ᵈ apd Coeq-elim (! (glue (inl (π₁ e))))
        =⟨ lemma _ _ (p e) (transp-↓' _ _ _) ∙ᵈₗ apd-! Coeq-elim (glue (inl (π₁ e))) ⟩
      lemma _ _ (p e) (transp-↓' _ _ _) ∙ᵈ !ᵈ (apd Coeq-elim (glue (inl (π₁ e))))
        =⟨ lemma _ _ (p e) (transp-↓' _ _ _) ∙ᵈₗ ap !ᵈ (PushoutElim.glue-β x ((λ v → transport X (glue (inl v)) (x v))) _ (inl (π₁ e))) ⟩
      lemma _ _ (p e) (transp-↓' _ _ _) ∙ᵈ !ᵈ (transp-↓' X (glue (inl (π₁ e))) _)
        =⟨ lemma2 _ _ (p e) (transp-↓' X (glue (inl (π₁ e))) _) ⟩
      p e
        =∎
      where
        lemma2 : {a b c : Coeq gph} (p : a == b) (q : c == b) {x : X a} {y : X b} {z : X c} → (r : x == z [ X ↓ (p ∙ ! q) ]) →
               (s : z == y [ X ↓ q ]) → lemma p q r s ∙ᵈ !ᵈ s == r
        lemma2 idp idp idp idp = idp

  Coeq-rec : ∀ {j} {X : Type j} (x : V → X) (p : (e : E) → x (π₀ e) == x (π₁ e)) →
            Coeq gph → X
  Coeq-rec {X = X} x p = Coeq-elim (λ _ → X) x λ e → ↓-cst-in (p e)


  Coeq-rec-β= : ∀ {j} {X : Type j} (x : V → X) (p : (e : E) → x (π₀ e) == x (π₁ e))
    (e : E) → ap (Coeq-rec x p) (quot e) == p e
  Coeq-rec-β= {X = X} x p e = apd=cst-in (Coeq-β= _ _ _ _)

  private
    E' : V → V → Type (lmax i j)
    E' u v = Σ E (λ e → (u == π₀ e) × (π₁ e == v))
    
