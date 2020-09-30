{-# OPTIONS --without-K --exact-split --rewriting --overlapping-instances #-}

open import lib.Basics
open import lib.NConnected
open import lib.NType2
open import lib.types.Truncation
open import lib.types.Sigma
open import lib.Equivalence
open import lib.types.Fin
open import lib.types.Coproduct

open import Graphs.Definition
open import Graphs.Properties

open import Coequalizers.Definition
open import Coequalizers.Misc
open import Groups.Definition
open import Coequalizers.PullbackStability
open import Coequalizers.PreserveEquivalence
open import Coequalizers.EdgeCoproduct
open import Graphs.SpanningTreeFinite
open import Graphs.SubTrees

open import Util.Misc
open import Util.DecEq

module NielsenSchreier {i : ULevel} where

{- We build towards the proof of the finite index Nielsen-Schreier theorem in several steps. -}

{- We will first show that subgroups of free higher groups are free higher groupoids. That is, we will show that
   for any family of types X over ⊤ / A, the total space Σ (⊤ / A) X is equivalent to the coequalizer of 
   a graph. Moveover, we can give an explicit description of the graph. -}
module SubgroupsOfFreeHigherGroups (A : Type i) (X : (⊤ / A) → Type i) where
  instance
    {- Whenever we need a pair of maps (A × X fhg-base) ⇉ (X fhg-base) we will use the definition below. This
       applies in this module and wherever it is imported. -}
    higher-subgp-gph : Graph (A × X fhg-base) (X fhg-base)
    higher-subgp-gph = record { π₀ = snd ; π₁ = λ {(a , x) → transport X (quot a) x} }


  to-free-higher-gpd : Σ (⊤ / A) X ≃ (X fhg-base) / (A × X fhg-base)
  to-free-higher-gpd =
      Σ (⊤ / A) X
        ≃⟨ pb-equiv ⁻¹ ⟩ -- coequalizers are stable under pullback
      (Σ ⊤ (X ∘ c[_])) / (Σ A (X ∘ c[_] ∘ π₀))
        ≃⟨ Coeq-emap Σ₁-Unit (ide _) (λ _ → idp) (λ _ → idp) ⟩
      (X fhg-base) / (A × X fhg-base)
        ≃∎
      where
        open PullbackStability A ⊤ X -- contains definition of (Σ ⊤ (X ∘ c[_])) / (Σ A (X ∘ c[_] ∘ π₀))
    

{- We now show that subgroups of free groups are free groupoids. This is a 1-truncated version of
   the result above. -}
module SubGroupsOfFreeGroups (A : Type i) (X : ∥ ⊤ / A ∥₁ → Type i)
  ⦃ Xset : {z : ∥ ⊤ / A ∥₁} → is-set (X z) ⦄ where -- we now need to assume X is 0-truncated.
  open SubgroupsOfFreeHigherGroups A (X ∘ [_]) public -- also defines instance for (X fhg-base) / (A × X fhg-base)

  to-free-gpd : Σ ∥ ⊤ / A ∥₁ X ≃ ∥ X base / (A × X base) ∥₁
  to-free-gpd =
      Σ ∥ ⊤ / A ∥₁ X
        ≃⟨ Σ-emap-r (Trunc-elim λ z → ide _) ⟩
      Σ ∥ ⊤ / A ∥₁ X'
        ≃⟨ TruncRecType.flattening-Trunc _ ⟩
      ∥ Σ (⊤ / A) (X ∘ [_]) ∥₁
        ≃⟨ Trunc-emap to-free-higher-gpd ⟩
      ∥ X base / (A × X base) ∥₁
        ≃∎
      where
        X'-set : ∥ ⊤ / A ∥₁ → hSet i
        X'-set = Trunc-rec (λ z → ((X [ z ]) , Xset))

        X' = fst ∘ X'-set

        instance
          X-≃-gpd : {z : ∥ ⊤ / A ∥₁} → is-gpd (X z ≃ X' z)
          X-≃-gpd {z} = raise-level 0 (≃-level Xset (snd (X'-set z)))


{- A free groupoid with vertex set a definitionally finite set is merely equivalent
   to a free group. -}
strict-fin-free-gpd-is-free-gp :
  (n : ℕ) → (E : Type i) → (Edec : has-dec-eq E) →
  ⦃ gph : Graph E (Fin (S n)) ⦄ ⦃ conn : gph-is-connected gph ⦄ →
  ∥ Σ (Type i) (λ B → ∥ Coeq gph ∥₁ ≃ FreeGroup B) ∥
strict-fin-free-gpd-is-free-gp n E Edec =
  Trunc-fmap from-spanning-tree-fin (spanning-tree E Edec n)
  where
    from-spanning-tree-fin : SpanningTree E (Fin (S n)) (Fin n) (Fin (S n)) →
      Σ (Type i) (λ B → ∥ Fin (S n) / E ∥₁ ≃ FreeGroup B)
    from-spanning-tree-fin st =
      ¬E' , Trunc-emap eq
      where
        open SpanningTree st
        open ExtendSpanningTree E (Fin (S n)) (Fin n) (Fin (S n)) st
        open CoeqCoprodEquiv (Fin (S n)) (Fin n) ¬E'

        eq : Fin (S n) / E ≃ ⊤ / ¬E'
        eq =
          Fin (S n) / E
            ≃⟨ spantree-equiv ⟩
          Fin (S n) / ((Fin n) ⊔ ¬E')
            ≃⟨ edge-coproduct-expand ⟩
          (Fin (S n) / (Fin n)) / ¬E'
            ≃⟨ Coeq-emap (contr-equiv-Unit ⟨⟩) (ide _) (λ _ → idp) (λ _ → idp) ⟩
          ⊤ / ¬E'
            ≃∎

{- We generalise the above so that the vertex set only needs to be equivalent to a 
   definitionally finite set. -}
fin-free-gpd-is-free-gp : (n : ℕ) → (E : Type i) → (Edec : has-dec-eq E) →
  (V : Type i) → (Vfin : V ≃ Fin (S n)) →
  ⦃ gph : Graph E V ⦄ ⦃ conn : gph-is-connected gph ⦄ →
  ∥ Σ (Type i) (λ B → ∥ Coeq gph ∥₁ ≃ FreeGroup B) ∥
fin-free-gpd-is-free-gp n E Edec V Vfin =
  Trunc-fmap (λ {(B , e) → B , (e ∘e Trunc-emap coeq-equiv)}) (strict-fin-free-gpd-is-free-gp n E Edec)
  where
    instance
      gph' : Graph E (Fin (S n))
      gph' = record { π₀ = (–> Vfin) ∘ π₀ ; π₁ = (–> Vfin) ∘ π₁ }

    coeq-equiv : (V / E) ≃ (Fin (S n) / E)
    coeq-equiv = Coeq-emap Vfin (ide E) (λ _ → idp) λ _ → idp

    instance
      conn' : gph-is-connected gph'
      conn' = equiv-preserves-level (Trunc-emap coeq-equiv )


{- We can now prove the finite index version of the Nielsen-Schreier theorem. -}
nielsen-schreier-finite-index :
  (A : Type i) (Adec : has-dec-eq A) -- we are given a type A with decidable equality
  (X : (FreeGroup A) → Type i) -- together with a covering space over the free group on A, that is a family of types X ...
  ⦃ conn : is-connected 0 (Σ (FreeGroup A) X) ⦄ -- such that the total space is connected
  (n : ℕ) (Xfin : X (base) ≃ Fin (S n)) → -- here we do the finite index case
  ∥ Σ (Type i) (λ B → Σ (FreeGroup A) X ≃ FreeGroup B) ∥ -- then the total space is a free group
  
nielsen-schreier-finite-index A Adec X n Xfin =
  Trunc-fmap (λ {(B , e) → B , e ∘e to-free-gpd}) -- we compose the two equivalences from earlier
             (fin-free-gpd-is-free-gp n (A × X base) (×-has-dec-eq Adec (equiv-preserves-dec-eq Xfin Fin-has-dec-eq)) (X base) Xfin)
               -- earlier we showed that free groupoids with finite vertex set are merely equivalent to free groups
  where
    open SubGroupsOfFreeGroups A X -- contains our proof that the subgroup is a free groupoid

    instance -- we use that X is a set and the free groupoid is connected
      Xset : {z : (FreeGroup A)} → is-set (X z)
      Xset {z} = Trunc-elim {P = λ z → is-set (X z)}
        (Coeq-elim (λ z → is-set (X [ z ]))
          (λ {unit → equiv-preserves-level (Xfin ⁻¹) ⦃ Fin-is-set ⦄}) λ _ → prop-has-all-paths-↓) z


      conn2 : is-connected 0 (X base / (A × X base))
      conn2 = equiv-preserves-level e
        where
          e : ∥ Σ (FreeGroup A) X ∥₀ ≃ ∥ X base / (A × X base) ∥₀
          e =
            ∥ Σ (FreeGroup A) X ∥₀
              ≃⟨ Trunc-emap (to-free-gpd ) ⟩
            ∥ ∥ X base / (A × X base) ∥₁ ∥₀
              ≃⟨ Trunc-fuse _ 0 1 ⟩
            ∥ X base / (A × X base) ∥₀
              ≃∎
