{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Fin
open import lib.types.Nat
open import lib.types.Empty
open import lib.NType2
open import lib.Equivalence2

open import Util.Misc
open import Util.Coproducts

{- Some useful lemmas about working with finite sets. E.g. An injection from a finite set
   to itself is an equivalence, an injection from a finite set to a large finite set has
   at least one element not in its image.
-}
module Util.Finite where

ℕ=-to-Fin= : {n : ℕ} {x y : Fin n} → (fst x == fst y) → x == y
ℕ=-to-Fin= p = pair= p prop-has-all-paths-↓

finite-lpo : {i : ULevel} {n : ℕ} (P : Fin n → Type i) (dec : (x : Fin n) → Dec (P x)) →
  (Σ (Fin n) P ⊔ ((x : Fin n) → ¬ (P x)))

finite-lpo {n = 0} P dec = inr (λ x _ → –> Fin-equiv-Empty x)
finite-lpo {i} {n = S n} P dec = ⊔-fmap (–> el) (–> er) lemma
  where
    P' : Fin n ⊔ ⊤ → Type i
    P' z = P (<– Fin-equiv-Coprod z)

    el : Σ (Fin n ⊔ ⊤) P' ≃ Σ (Fin (S n)) P
    el = Σ-emap-l P (Fin-equiv-Coprod ⁻¹)

    er : ((x : Fin n ⊔ ⊤) → ¬ (P' x)) ≃ ((x : Fin (S n)) → ¬ (P x))
    er = Π-emap-l (¬ ∘ P) (Fin-equiv-Coprod ⁻¹)

    lemma : Σ (Fin n ⊔ ⊤) P' ⊔ ((x : Fin n ⊔ ⊤) → ¬ (P' x))
    lemma = ⊔-rec (λ np → inl ((inl (fst np)) , (snd np)))
      (λ f → ⊔-rec (λ p → inl ((inr unit) , p)) (λ np → inr (λ { (inl k) → f k ; (inr _) → np})) (dec (n , ltS))) (finite-lpo {n = n} (P' ∘ inl) λ x → dec (<– Fin-equiv-Coprod (inl x)))

fin-img-dec : {i : ULevel} {A : Type i} (dec : has-dec-eq A) {n : ℕ} (inc : Fin n → A) → (a : A) → ((hfiber inc a) ⊔ ¬ (hfiber inc a))
fin-img-dec dec inc a = ⊔-rec (λ np → inl np) (λ f → inr (λ np → f (fst np) (snd np))) (finite-lpo (λ k → inc k == a) λ k → dec (inc k) a)    

Fin-eq : {n : ℕ} {x y : Fin n} → (fst x == fst y) → x == y
Fin-eq p = pair= p prop-has-all-paths-↓

<-or-≥ : (n m : ℕ) → ((n < m) ⊔ (m ≤ n))
<-or-≥ n m = ⊔-rec (λ p → inr (inl (! p))) (⊔-rec inl (λ l → inr (inr l))) (ℕ-trichotomy n m)

≤-or-> : (n m : ℕ) → ((n ≤ m) ⊔ (m < n))
≤-or-> m n = ⊔-rec (inl ∘ inl) (⊔-fmap inr (idf _)) (ℕ-trichotomy m n)

<-≤-trans : {l m n : ℕ} → (l < m) → (m ≤ n) → (l < n)
<-≤-trans p (inl q) = transport _ q p
<-≤-trans p (inr q) = <-trans p q

≤-<-trans : {l m n : ℕ} → (l ≤ m) → (m < n) → (l < n)
≤-<-trans (inl p) q = transport _ (! p) q
≤-<-trans (inr p) q = <-trans p q

<S≠-to-< : {a b : ℕ} → (a < S b) → (a ≠ b) → (a < b)
<S≠-to-< ltS ne = ⊥-elim (ne idp)
<S≠-to-< (ltSR lt) ne = lt

module _ {n : ℕ} (k : Fin n) where
  private
    degeneracy-aux : (x : Fin (S n)) → ((fst x ≤ fst k) ⊔ (fst k < fst x)) → Fin n
    degeneracy-aux x (inl z) = (fst x) , ≤-<-trans z (snd k)
    degeneracy-aux (.(S (fst k)) , snd) (inr ltS) = k
    degeneracy-aux (.(S _) , snd) (inr (ltSR z)) = _ , (<-cancel-S snd)

    degeneracy-almost-inj-aux : {x y : Fin (S n)} → (fst x ≠ fst k) → (fst y ≠ fst k) →
      (z : ((fst x) ≤ (fst k)) ⊔ ((fst k) < (fst x))) → (w : ((fst y) ≤ (fst k)) ⊔ ((fst k) < (fst y))) →
      (degeneracy-aux x z == degeneracy-aux y w) → x == y

    degeneracy-almost-inj-aux f g (inl z) (inl w) p = ℕ=-to-Fin= (ap fst p)
    degeneracy-almost-inj-aux f g (inl z) (inr ltS) p = ⊥-rec (f (ap fst p))
    degeneracy-almost-inj-aux f g (inl z) (inr (ltSR w)) p = ⊥-rec (<-to-≠ (≤-<-trans z w) (ap fst p))
    degeneracy-almost-inj-aux f g (inr ltS) (inl w) p = ⊥-rec (g (ap fst (! p)))
    degeneracy-almost-inj-aux f g (inr (ltSR z)) (inl w) p = ⊥-rec (<-to-≠ (≤-<-trans w z) (ap fst (! p)))
    degeneracy-almost-inj-aux f g (inr ltS) (inr ltS) p = ℕ=-to-Fin= idp
    degeneracy-almost-inj-aux f g (inr ltS) (inr (ltSR w)) p = ℕ=-to-Fin= (ap S (ap fst p))
    degeneracy-almost-inj-aux f g (inr (ltSR z)) (inr ltS) p = ℕ=-to-Fin= (ap S (ap fst p))
    degeneracy-almost-inj-aux f g (inr (ltSR z)) (inr (ltSR w)) p = ℕ=-to-Fin= (ap S (ap fst p))

  abstract
    degeneracy : (x : Fin (S n)) → Fin n
    degeneracy x = degeneracy-aux x (≤-or-> _ _)

    degeneracy-almost-inj : {x y : Fin (S n)} → (fst x ≠ fst k) → (fst y ≠ fst k) →
      (degeneracy x == degeneracy y) → x == y
    degeneracy-almost-inj f g = degeneracy-almost-inj-aux f g (≤-or-> _ _) (≤-or-> _ _)

Fin-hfiber-dec : {i : ULevel} {X : Type i} {n : ℕ} (dec : has-dec-eq X) → (f : Fin n → X) →
  (x : X) → Dec (hfiber f x)

Fin-hfiber-dec dec f x = ⊔-fmap (idf _) (λ g p → g (fst p) (snd p))
  (finite-lpo (λ z → f z == x) (λ z → dec (f z) x))


Fin-inj-to-surj : (n : ℕ) → (inc : Fin n → Fin n) → (inc-inj : is-inj inc) → (y : Fin n) → hfiber inc y
Fin-inj-to-surj O inc inc-inj y = ⊥-rec (–> Fin-equiv-Empty y)
Fin-inj-to-surj (S n) inc inc-inj y =
  ⊔-rec (λ p → n<Sn , (! p))
        (λ f → ⊔-rec (λ p → case1 p f) (λ g → case2 g f) (Fin-has-dec-eq k n<Sn))
        (Fin-has-dec-eq y k)
  where
    n<Sn = (n , ltS)
    k = inc n<Sn

    case1 : k == n<Sn → (y ≠ k) → hfiber inc y
    case1 p f = Fin-S (fst x') , ℕ=-to-Fin= (ap fst (snd x'))
      where
        inc' : Fin n → Fin n
        inc' x = (fst (inc (Fin-S x))) , <S≠-to-< (snd (inc (Fin-S x))) λ q → <-to-≠ (snd x) (ap fst (inc-inj _ _ (ℕ=-to-Fin= q ∙ ! p)))

        inc-inj' : is-inj inc'
        inc-inj' x x' p = Fin-S-is-inj _ _ (inc-inj _ _ (ℕ=-to-Fin= (ap fst p)))

        y' : Fin n
        y' = (fst y) , (<S≠-to-< (snd y) (λ q → f (ℕ=-to-Fin= q ∙ ! p)))

        x' : hfiber inc' y'
        x' = Fin-inj-to-surj n inc' inc-inj' y'

    case2 : k ≠ n<Sn → (y ≠ k) → hfiber inc y
    case2 f g = Fin-S (fst x') , degeneracy-almost-inj k' (λ q → <-to-≠ (snd (fst x')) (ap fst (inc-inj (Fin-S (fst x')) n<Sn (ℕ=-to-Fin= q))))
                                                            (λ q → g (ℕ=-to-Fin= q)) (snd x')
      where
        k' = (fst k) , (<S≠-to-< (snd k) (λ q → f (ℕ=-to-Fin= q)))

        inc' : Fin n → Fin n
        inc' x = degeneracy k' (inc (Fin-S x))

        inc-inj' : is-inj inc'
        inc-inj' x x' p =
          Fin-S-is-inj _ _ (inc-inj _ _ (degeneracy-almost-inj k' (λ q → <-to-≠ (snd x) (ap fst (inc-inj _ _ (ℕ=-to-Fin= q))))
                                                                  (λ q → <-to-≠ (snd x') (ap fst (inc-inj _ _ (ℕ=-to-Fin= q))))
                                                                  p))

        x' : hfiber inc' (degeneracy k' y)
        x' = Fin-inj-to-surj n inc' inc-inj' ((degeneracy k' y))

Fin-inj-to-equiv : {n : ℕ} → (inc : Fin (S n) → Fin (S n)) → (inc-inj : is-inj inc) → (is-equiv inc)
Fin-inj-to-equiv inc inc-inj =
  contr-map-is-equiv λ x → inhab-prop-is-contr (Fin-inj-to-surj _ inc inc-inj x) ⦃ inj-to-embed ⦃ Fin-is-set ⦄ inc inc-inj x ⦄


Fin-smaller-is-smaller : {m n : ℕ} (l : m < n) (f : Fin m → Fin n) → Σ (Fin n) (λ k → ¬ (hfiber f k))
Fin-smaller-is-smaller {m} {n} l f = ⊔-cancel-r (finite-lpo _ (λ k → ⊔-rec (λ x → inr (λ g → g x)) inl (Fin-hfiber-dec Fin-has-dec-eq f k))) lemma
  where
    lemma : ((k : Fin n) → ¬ (¬ (hfiber f k))) → ⊥
    lemma g = <-to-≠ (snd (g'' (fst k))) (ap fst (snd k))
      where
        g' : (k : Fin n) → (hfiber f k)
        g' k = ⊔-cancel-r (Fin-hfiber-dec Fin-has-dec-eq f k) (g k)

        g'' : Fin n → Fin m
        g'' = fst ∘ g'

        g''-is-inj : is-inj g''
        g''-is-inj y y' p = ! (snd (g' y)) ∙ ap f p ∙ snd (g' y')

        h : Fin n → Fin n
        h k = (fst (g'' k)) , (<-trans (snd (g'' k)) l)

        h-is-inj : is-inj h
        h-is-inj x y p = g''-is-inj _ _ (ℕ=-to-Fin= (ap fst p))

        k : hfiber h (m , l)
        k = Fin-inj-to-surj n h h-is-inj ((m , l))
        
