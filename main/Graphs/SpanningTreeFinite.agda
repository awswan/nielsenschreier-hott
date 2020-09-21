{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Basics
open import lib.types.Truncation
open import lib.types.Fin
open import lib.types.Nat
open import lib.types.Empty
open import lib.types.Unit
open import lib.types.Coproduct
open import lib.types.Sigma
open import lib.types.Paths
open import lib.NConnected

open import Util.Misc
open import Util.Finite
open import Util.Coproducts

open import Graphs.Definition
open import Graphs.Properties

open import Coequalizers.Definition
open import Coequalizers.PreserveEquivalence
open import Coequalizers.EdgeCoproduct
open import Coequalizers.Misc
open import Graphs.SubTrees

{- We show that graphs with finite vertex set have spanning trees. -}
module Graphs.SpanningTreeFinite {i : ULevel} where

module _ (E : Type i) (V : Type i) ⦃ gph : Graph E V ⦄ where

instance
  noedges : {j : ULevel} {V : Type j} → Graph ⊥ V -- defines the trivial coequalizer V / ⊥
  noedges = record { π₀ = ⊥-elim ; π₁ = ⊥-elim }

noedge-triv : {j : ULevel} {V : Type j} → V / ⊥ ≃ V
noedge-triv {V = V} = f , (record { g = c[_] ; f-g = f-g ; g-f = g-f ; adj = adj })
  where
    f : V / ⊥ → V
    f = Coeq-rec (idf V) (λ _ → idp)

    f-g : (v : V) → (f (c[ v ]) == v)
    f-g v = idp

    g-f : (z : V / ⊥) → (c[ (f z) ] == z)
    g-f = Coeq-elim _ (λ _ → idp) ⊥-elim

    adj : (z : V / ⊥) → ap f (g-f z) == idp
    adj = Coeq-elim _ (λ _ → idp) ⊥-elim


{- A spanning tree is a subtree where the inclusion of vertex sets is an
   equivalence and the inclusion of edge sets is complemented.
-}
record SpanningTree {j k l : ULevel} (E : Type i) (V : Type j) ⦃ gph : Graph E V ⦄
    (E' : Type k) (V' : Type l) : Type (lmax (lmax i j) (lmax l k)) where
  field
    is-st : SubTree E V E' V'
  open SubTree is-st public
  field
    all-vertices : is-equiv inU
    is-complemented : E ≃ E' ⊔ Σ E (λ e → ¬ (hfiber inD e))
    inD-comm : inD ∼ (<– is-complemented) ∘ inl

module ExtendSpanningTree {j k l : ULevel} (E : Type i) (V : Type j) ⦃ gph : Graph E V ⦄
  (E' : Type k) (V' : Type l) (spantree : SpanningTree E V E' V') where

  open SpanningTree spantree

  ¬E' = Σ E (λ e → ¬ (hfiber (SubTree.inD is-st) e))

  instance
    gph-coprod : Graph (E' ⊔ ¬E') V'
    gph-coprod = record { π₀ = ⊔-rec π₀ λ e → is-equiv.g all-vertices (π₀ (<– is-complemented (inr e)))
                       ; π₁ = ⊔-rec π₁ λ e → is-equiv.g all-vertices (π₁ (<– is-complemented (inr e))) }


  inU-equiv : V' ≃ V
  inU-equiv = (inU , all-vertices)

  spantree-equiv : V / E ≃ V' / (E' ⊔ ¬E')
  spantree-equiv = (Coeq-emap inU-equiv (is-complemented ⁻¹)
                   (λ { (inl e') → ! (comm₀ e') ∙ ap π₀ (inD-comm e') ; (inr x) → <–-inv-r inU-equiv _})
                   λ { (inl e') → ! (comm₁ e') ∙ ap π₁ (inD-comm e') ; (inr x) → <–-inv-r inU-equiv _}) ⁻¹


composepp : {j k l : ULevel} {E' : Type j} {E : Type k} {V : Type l} ( inc : E' → E ) ⦃ gph : Graph E V ⦄ → Graph E' V
composepp inc ⦃ gph = gph ⦄ = record { π₀ = P.π₀ ∘ inc ; π₁ = P.π₁ ∘ inc }
    where
      module P = Graph gph

Fin-equiv-Unit : Fin 1 ≃ ⊤
Fin-equiv-Unit =
  Fin 1
    ≃⟨ Fin-equiv-Coprod ⟩
  Fin 0 ⊔ ⊤
    ≃⟨ ⊔-emap Fin-equiv-Empty (ide ⊤) ⟩
  ⊥ ⊔ ⊤
    ≃⟨ ⊔₁-Empty ⊤ ⟩
  ⊤
    ≃∎

compose-equiv-subtree-l : {j k l m n : ULevel} {E : Type i} {V : Type j} ⦃ gph : Graph E V ⦄
  (D : Type k) (U : Type l) (D' : Type m) (U' : Type n) → (D' ≃ D) → (U' ≃ U) →
  SubTree E V D U → SubTree E V D' U'

compose-equiv-subtree-l D U D' U' equivD equivU (subtree inD inU D-inj U-inj U-dec comm₀ comm₁) =
  subtree (inD ∘ –> equivD) (inU ∘ –> equivU) (∘-is-inj D-inj (–>-is-inj equivD)) (∘-is-inj U-inj (–>-is-inj equivU))
          (λ v → ⊔-rec (λ {(u , p) → inl ((<– equivU u) , (ap inU (<–-inv-r equivU u) ∙ p))})
                          (λ f → inr (λ {(u , p) → f ((–> equivU u) , p) })) (U-dec v))
          (λ d → comm₀ (–> equivD d) ∙ ap inU (! (<–-inv-r equivU _)))
          (λ d → comm₁ (–> equivD d) ∙ ap inU (! (<–-inv-r equivU _)))
  where
    instance
      gph' : Graph D' U'
      gph' = record { π₀ = λ d → <– equivU (π₀ (–> equivD d)) ; π₁ = λ d → <– equivU (π₁ (–> equivD d)) }

      c : is-contr (U' / D')
      c = equiv-preserves-level ((Coeq-emap equivU equivD (λ d → <–-inv-r equivU _) λ d → <–-inv-r equivU _) ⁻¹)

{- Since the vertex set is finite, we can build the spanning tree up a step at a time. -}
build-spanning-tree : (E : Type i) (n : ℕ) ⦃ gph : Graph E (Fin (S n)) ⦄ ⦃ conn : gph-is-connected gph ⦄ →
  (k : ℕ) → (k < S n) → ∥ SubTree E (Fin (S n)) (Fin k) (Fin (S k)) ∥

build-spanning-tree E n O l =
  [ compose-equiv-subtree-l _ _ _ _ Fin-equiv-Empty Fin-equiv-Unit t ]
  where
    instance
      ic : is-contr (⊤ / ⊥)
      ic = equiv-preserves-level (noedge-triv ⁻¹)
      
    t : SubTree E (Fin (S n)) ⊥ ⊤
    t = subtree ⊥-elim (λ _ → 0 , l) ⊥-elim (λ {unit unit _ → idp}) (λ v → ⊔-fmap (λ p → unit , (! p)) (λ {f (unit , p) → f (! p)}) (Fin-has-dec-eq v (0 , l)))
                ⊥-elim ⊥-elim

build-spanning-tree E n (S k) l =
  do
    ih ← (build-spanning-tree E n k (<-trans ltS l))
    let x = Fin-smaller-is-smaller l (SubTree.inU ih)
    t ← (extend-subtree E (Fin (S n)) Fin-has-dec-eq ih (fst x) (snd x))
    [ compose-equiv-subtree-l _ _ _ _ (⊔-sym ∘e Fin-equiv-Coprod) Fin-equiv-Coprod t ]
    

spanning-tree : (E : Type i) (Edec : has-dec-eq E) (n : ℕ) ⦃ gph : Graph E (Fin (S n)) ⦄ ⦃ conn : gph-is-connected gph ⦄ →
  ∥ SpanningTree E (Fin (S n)) (Fin n) (Fin (S n)) ∥

spanning-tree E Edec n = Trunc-fmap from-subtree (build-spanning-tree E _ _ ltS)
  where
    from-subtree : SubTree E (Fin (S n)) (Fin n) (Fin (S n)) → SpanningTree E (Fin (S n)) (Fin n) (Fin (S n))
    from-subtree st@(subtree ⦃ gphDU ⦄ inD inU D-inj U-inj U-dec comm₀ comm₁) =
      record
        { is-st = st
        ; all-vertices = Fin-inj-to-equiv inU U-inj
        ; is-complemented = dec-img-to-⊔ inD D-inj (Fin-hfiber-dec Edec inD) ⁻¹
        ; inD-comm = λ _ → idp
        }

