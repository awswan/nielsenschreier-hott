{-# OPTIONS --without-K --overlapping-instances #-}

open import lib.Basics
open import lib.types.Coproduct
open import lib.types.Truncation
open import lib.types.Sigma
open import lib.types.Empty
open import lib.types.Bool
open import lib.NConnected
open import lib.NType2

module Util.Misc where

transp-↓' : ∀ {k j} {A : Type k} (P : A → Type j) {a₁ a₂ : A}
  (p : a₁ == a₂) (y : P a₁) → y == transport P p y [ P ↓ p ]
transp-↓' P p y = from-transp P p idp

Σ-transp : ∀ {i j} {A : Type i} (B : A → Type j) {a a' : A} (p : a == a') (b : B a) →
           (a , b) == (a' , transport B p b)

Σ-transp B p b = pair= p (transp-↓' B p b)


equiv-prop : {i j : ULevel} {P : Type i} ⦃ P-prop : is-prop P ⦄ {Q : Type j} ⦃ Q-prop : is-prop Q ⦄ → (P → Q) →
             (Q → P) → (P ≃ Q)

equiv-prop f g = f , (record { g = g ; f-g = λ q → prop-has-all-paths (f (g q)) q
                             ; g-f = λ p → prop-has-all-paths (g (f p)) p
                             ; adj = λ p → prop-has-all-paths _ _ })

_↔_ : {i j : ULevel} (A : Type i) (B : Type j) → Type (lmax i j)
A ↔ B = (A → B) × (B → A)

prop-extensionality : {i : ULevel} {P Q : Type i} ⦃ P-prop : is-prop P ⦄ ⦃ Q-prop : is-prop Q ⦄ → (P ↔ Q) → (P == Q)
prop-extensionality e = ua (equiv-prop (fst e) (snd e))

{- Notation for propositional truncation. -}
∥_∥ : {j : ULevel} → (A : Type j) → Type j
∥_∥ = Trunc (-1)

{- This enables do notation for propositional truncation. It works well for any modality, but we will
   only need this special case. -}
_>>=_ : {i j : ULevel} {X : Type i} {Y : Type j} → (Trunc (-1) X) → (X → Trunc (-1) Y) → (Trunc (-1) Y)
x >>= f = Trunc-rec f x

{- We also add notation for 0 and 1 truncation -}
∥_∥₀ : {j : ULevel} → (A : Type j) → Type j
∥_∥₀ = Trunc 0

∥_∥₁ : {j : ULevel} → (A : Type j) → Type j
∥_∥₁ = Trunc 1


conn-to-path : {i : ULevel} {A : Type i} ⦃ conn : is-connected 0 A ⦄ → (a b : A) → ∥ a == b ∥
conn-to-path ⦃ conn ⦄ _ _ = contr-center (path-conn conn)

conn-to-inh : {i : ULevel} {A : Type i} ⦃ conn : is-connected 0 A ⦄ → ∥ A ∥
conn-to-inh ⦃ conn ⦄ = Trunc-rec ⦃ raise-level _ ⟨⟩ ⦄ [_] (contr-center conn)

inj-to-embed-allpaths : {i j : ULevel} {A : Type i} {B : Type j} ⦃ Bset : is-set B ⦄ (inc : A → B) (inc-inj : is-inj inc) → (b : B) → has-all-paths (hfiber inc b)
inj-to-embed-allpaths inc inc-inj b (a , p) (a' , q) = pair= (inc-inj _ _ (p ∙ ! q)) prop-has-all-paths-↓

inj-to-embed : {i j : ULevel} {A : Type i} {B : Type j} ⦃ Bset : is-set B ⦄ (inc : A → B) (inc-inj : is-inj inc) → (b : B) → is-prop (hfiber inc b)
inj-to-embed inc inc-inj b = all-paths-is-prop (inj-to-embed-allpaths inc inc-inj b)

dec-img-to-⊔ : {i j : ULevel} {A : Type i} {B : Type j} (inc : A → B) (inc-inj : is-inj inc) (dec-img : (b : B) → Dec (hfiber inc b)) → A ⊔ Σ B (λ b → ¬ (hfiber inc b)) ≃ B
dec-img-to-⊔ {A = A} {B = B} inc inc-inj dec-img = equiv f g f-g g-f
  where
    g-aux : (b : B) → (Dec (hfiber inc b)) → A ⊔ Σ B (λ b → ¬ (hfiber inc b))
    g-aux b (inl x) = inl (fst x)
    g-aux b (inr x) = inr (b , x)

    g : (b : B) → A ⊔ Σ B (λ b → ¬ (hfiber inc b))
    g b = g-aux b (dec-img b)

    f : A ⊔ Σ B (λ b → ¬ (hfiber inc b)) → B
    f (inl a) = inc a
    f (inr (b , p)) = b

    g-f-aux : (z : A ⊔ Σ B (λ b → ¬ (hfiber inc b))) (x : Dec (hfiber inc (f z))) → (g-aux (f z) x == z)
    g-f-aux (inl a) (inl x) = ap inl (inc-inj _ _ (snd x))
    g-f-aux (inl a) (inr x) = ⊥-rec (x (a , idp))
    g-f-aux (inr p) (inl x) = ⊥-rec (snd p x)
    g-f-aux (inr p) (inr x) = ap inr (pair= idp (λ= λ w → prop-has-all-paths _ _))

    g-f : (z : A ⊔ Σ B (λ b → ¬ (hfiber inc b))) → (g (f z) == z)
    g-f z = g-f-aux z (dec-img (f z))

    f-g-aux : (b : B) → (x : Dec (hfiber inc b)) → (f (g-aux b x) == b)
    f-g-aux b (inl x) = snd x
    f-g-aux b (inr x) = idp

    f-g : (b : B) → (f (g b) == b)
    f-g b = f-g-aux b (dec-img b)

