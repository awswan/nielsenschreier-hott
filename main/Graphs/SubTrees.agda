{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Basics
open import lib.PathGroupoid
open import lib.types.Bool
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Coproduct
open import lib.types.Unit
open import lib.types.Empty
open import lib.NConnected
open import lib.NType
open import lib.NType2
open import lib.Equivalence
open import lib.types.Truncation

open import Util.Misc

open import Graphs.Definition
open import Graphs.Properties

open import Coequalizers.Definition
open import Coequalizers.EdgeCoproduct
open import Coequalizers.PreserveEquivalence
open import Coequalizers.TrivialExtension


{- Contains a useful lemma about extending subtrees used in the construction of spanning trees. -}
module Graphs.SubTrees where


{- We fix a graph E ⇉ V together with a family of types P over the vertex set. -}
module _ {i j k : ULevel} (E : Type i) (V : Type j) ⦃ gph : Graph E V ⦄
  (P : V → Type k) where
  private
    ijk' = lmax i (lmax j k)


  {- A crossing edge is an edge that has one end in P and one end outside P. -}
  record Crossingedge : Type ijk' where
    constructor
      crossingedge
    field
      edge : E
      dir : Bool
      end-in-P : P (Bool-rec (π₀ edge) (π₁ edge) dir)
      end-notin-P : ¬ (P (Bool-rec (π₁ edge) (π₀ edge) dir))


  {- If the graph is connected, P is decidable and we are given a vertex in P and a vertex outside P,
     then we can show there mereley exists an edge that crosses from P to ¬ P or vice versa. -}
  findedge : (dec : (v : V) → Dec (P v))  (u v : V) (uInP : P u) (vNotinP : ¬ (P v)) (p : c[ u ] == c[ v ] :> V / E) → ∥ Crossingedge ∥
  findedge dec u v uInP vNotinP p = equal-to-X c[ v ] p vNotinP
    where
      edgeequiv : (e : E) → ((¬ (P (π₀ e)) → ∥ Crossingedge ∥) ↔ (¬ (P (π₁ e)) → ∥ Crossingedge ∥))
      edgeequiv e =
        ⊔-rec
          (λ p0 → ⊔-rec
            (λ p1 → (λ _ f → ⊥-elim (f p1)) , λ _ f → ⊥-elim (f p0))
            (λ np1 → haveedge (crossingedge e true p0 np1))
            (dec (π₁ e)))
          (λ np0 → ⊔-rec
            (λ p1 → haveedge (crossingedge e false p1 np0))
            (λ np1 → (λ f _ → f np0) , λ f _ → f np1)
            (dec (π₁ e)))
          (dec ((π₀ e)))
          where
            haveedge : Crossingedge → ((¬ (P (π₀ e)) → ∥ Crossingedge ∥) ↔ (¬ (P (π₁ e)) → ∥ Crossingedge ∥))
            haveedge ce = (λ _ _ → [ ce ]) , λ _ _ → [ ce ]

      {- The key to the proof is to define a family of propositions X over the coequalizer of the graph. 
         For this to be well defined we need the lemma edgeequiv above, together with 
         propositional extensionality.
      -}
      X : V / E → Type (lmax j (lmax i k))
      X = Coeq-rec (λ v' → ¬ (P v') → ∥ Crossingedge ∥ ) (λ e → prop-extensionality (edgeequiv e))

      equal-to-X : (z : V / E) (p : c[ u ] == z) → X z
      equal-to-X .(c[ u ]) idp = λ nu → ⊥-elim (nu uInP)


module _ {i j k l : ULevel} (E : Type i) (V : Type j) ⦃ gph : Graph E V ⦄ where
  {- A subtree of E ⇉ V consists of a graph D ⇉ U such that U / D is contractible
     together with injection D ↪ E and decidable injection U ↪ V making the obvious squares commute. -}
  record SubTree (D : Type k) (U : Type l) : Type (lmax (lmax i j) (lmax k l)) where
    constructor subtree
    field
      ⦃ gphDU ⦄ : Graph D U
      inD : D → E
      inU : U → V
      D-inj : is-inj inD
      U-inj : is-inj inU
      U-dec : (v : V) → Dec (hfiber inU v)
      comm₀ : π₀ ∘ inD ∼ inU ∘ π₀
      comm₁ : π₁ ∘ inD ∼ inU ∘ π₁
      ⦃ DUistree ⦄ : is-tree gphDU

  {- If we are given subtree D ⇉ U and a vertex in V ∖ U, then we can extend the 
     subtree to a slightly larger one that contains one new vertex.
  -}
  extend-subtree : {D : Type k} {U : Type l} ⦃ conn : gph-is-connected gph ⦄ (decV : has-dec-eq V)  → (t : SubTree D U) → (v : V) → ¬ (hfiber (SubTree.inU t) v) →
                   ∥ SubTree (⊤ ⊔ D) (U ⊔ ⊤) ∥
  extend-subtree {D} {U} decV record { gphDU = gphDU ; inD = inD ; inU = inU ; D-inj = D-inj ; U-inj = U-inj ; comm₀ = comm₀ ; comm₁ = comm₁ ; U-dec = U-dec} v f =
    do -- we use do notation to help deal with iterated recursion on propositional truncation (see the definion of >>= in Util/Misc.agda)
      u ← (Coeq-rec [_] (λ e → prop-has-all-paths _ _) (contr-center (⟨⟩ :> is-tree gphDU)))
      p ← (conn-to-path c[ inU u ] c[ v ])
      ce ← (findedge E V (hfiber inU) U-dec (inU u) v (u , idp) f p)
      [ from-ce ce ]
    where
      from-ce : Crossingedge E V (λ v → (hfiber inU v)) → (SubTree (⊤ ⊔ D) (U ⊔ ⊤))
      from-ce (crossingedge edge true end-in-P end-notin-P) =
        record
          { inD = λ { (inl _) → edge ; (inr d) → inD d}
          ; inU = λ { (inl u) → inU u ; (inr _) → π₁ edge}
          ; D-inj = λ { (inl unit) →
                        λ { (inl unit) _ → idp ; (inr d) p → ⊥-elim (end-notin-P ((π₁ d) , ! (ap π₁ p ∙ comm₁ d)))}
                      ; (inr d) →
                        λ { (inl unit) p → ⊥-elim (end-notin-P ((π₁ d) , ! (comm₁ d) ∙ ap π₁ p)) ; (inr d') p → ap inr (D-inj _ _ p)}}
          ; U-inj = λ { (inl u) →
                        λ { (inl u') p → ap inl (U-inj _ _ p) ; (inr unit) p → ⊥-elim (end-notin-P (u , p))}
                      ; (inr unit) →
                        λ { (inl u) p → ⊥-elim (end-notin-P (u , (! p))) ; (inr unit) _ → idp}}
          ; U-dec = λ v → ⊔-rec (λ {(u , p) → inl ((inl u) , p)})
                                   (λ f → ⊔-rec (λ p → inl ((inr unit) , ! p))
                                                (λ g → inr (λ {(inl u , p) → f ((u , p)) ; (inr unit , p) → g (! p)}))
                                                (decV v (π₁ edge)))
                                   (U-dec v)
          ; comm₀ = λ { (inl x) → ! (snd end-in-P) ; (inr d) → comm₀ d}
          ; comm₁ = λ { (inl _) → idp ; (inr d) → comm₁ d}
          ; DUistree = equiv-preserves-level (extn-equiv ⁻¹)
          }
        where
          instance
            gphDU' : Graph (⊤ ⊔ D) (U ⊔ ⊤)
            gphDU' = record { π₀ = λ { (inl _) → inl (fst end-in-P) ; (inr x) → inl (π₀ x) }
                           ; π₁ = λ { (inl _) → inr unit ; (inr x) → inl (π₁ x) }}

            extn-equiv : (U ⊔ ⊤) / (⊤ ⊔ D) ≃ U / D
            extn-equiv =
              (U ⊔ ⊤) / (⊤ ⊔ D)
                ≃⟨ edge-coproduct-expand ⟩
              ((U ⊔ ⊤) / ⊤) / D
                ≃⟨ (Coeq-emap (TExtensionCoeq-l.extn-equiv (fst end-in-P)) (ide D) (λ _ → idp) λ _ → idp) ⁻¹ ⟩
              U / D
                ≃∎
              where
                open CoeqCoprodEquiv (U ⊔ ⊤) ⊤ D -- also defines instances for (U ⊔ ⊤) / ⊤) / D



      from-ce (crossingedge edge false end-in-P end-notin-P) =
        record
          { inD = λ { (inl _) → edge ; (inr d) → inD d}
          ; inU = λ { (inl u) → inU u ; (inr _) → π₀ edge}
          ; D-inj = λ { (inl unit) →
                        λ { (inl unit) _ → idp ; (inr d) p → ⊥-elim (end-notin-P ((π₀ d) , ! (ap π₀ p ∙ comm₀ d)))}
                      ; (inr d) →
                        λ { (inl unit) p → ⊥-elim (end-notin-P ((π₀ d) , ! (comm₀ d) ∙ ap π₀ p)) ; (inr d') p → ap inr (D-inj _ _ p)}}
          ; U-inj = λ { (inl u) →
                        λ { (inl u') p → ap inl (U-inj _ _ p) ; (inr unit) p → ⊥-elim (end-notin-P (u , p))}
                      ; (inr unit) →
                        λ { (inl u) p → ⊥-elim (end-notin-P (u , (! p))) ; (inr unit) _ → idp}}
          ; U-dec = λ v → ⊔-rec (λ {(u , p) → inl ((inl u) , p)})
                                   (λ f → ⊔-rec (λ p → inl ((inr unit) , ! p))
                                                (λ g → inr (λ {(inl u , p) → f ((u , p)) ; (inr unit , p) → g (! p)}))
                                                (decV v (π₀ edge)))
                                   (U-dec v)
          ; comm₀ = λ { (inl _) → idp ; (inr d) → comm₀ d}
          ; comm₁ = λ { (inl x) → ! (snd end-in-P) ; (inr d) → comm₁ d}
          ; DUistree = equiv-preserves-level (extn-equiv ⁻¹)
          }
          where
            instance
              gphDU' : Graph (⊤ ⊔ D) (U ⊔ ⊤)
              gphDU' = record { π₀ = λ { (inl _) →  inr unit ; (inr x) → inl (π₀ x) }
                             ; π₁ = λ { (inl _) → inl (fst end-in-P) ; (inr x) → inl (π₁ x) }}

              extn-equiv : (U ⊔ ⊤) / (⊤ ⊔ D) ≃ U / D
              extn-equiv =
                (U ⊔ ⊤) / (⊤ ⊔ D)
                  ≃⟨ edge-coproduct-expand ⟩
                ((U ⊔ ⊤) / ⊤) / D
                    ≃⟨ Coeq-emap (TExtensionCoeq-r.extn-equiv (fst end-in-P)) (ide D) (λ _ → idp) (λ _ → idp) ⁻¹ ⟩
                U / D
                  ≃∎
                where
                  open CoeqCoprodEquiv (U ⊔ ⊤) ⊤ D -- also defines instances for (U ⊔ ⊤) / ⊤) / D
        
