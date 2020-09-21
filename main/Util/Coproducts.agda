{-# OPTIONS --without-K #-}

open import lib.Basics
open import lib.types.Bool
open import lib.types.Coproduct
open import lib.types.Truncation
open import lib.types.Sigma
open import lib.types.Pi
open import lib.types.Fin
open import lib.types.Nat
open import lib.types.Empty
open import lib.NConnected
open import lib.NType2
open import lib.Equivalence2

{- Some miscellaneous lemmas about coproducts. -}
module Util.Coproducts where

⊔-fmap-is-equiv : {i j i' j' : ULevel} {A : Type i} {B : Type j} {A' : Type i'} {B' : Type j'}
  (f : A → A') (g : B → B') (f-eq : is-equiv f) (g-eq : is-equiv g) → is-equiv (⊔-fmap f g)

⊔-fmap-is-equiv f g f-eq g-eq =
  record { g = ⊔-fmap Feq.g Geq.g
         ; f-g = Coprod-elim (λ a → ap inl (Feq.f-g a)) λ b → ap inr (Geq.f-g b)
         ; g-f = Coprod-elim (λ a → ap inl (Feq.g-f a)) (λ b → ap inr (Geq.g-f b))
         ; adj = Coprod-elim (λ a → ∘-ap (⊔-fmap f g) inl _ ∙ ap-∘ _ _ _ ∙ ap (ap inl) (Feq.adj a))
                             λ b →  ∘-ap (⊔-fmap f g) _ _ ∙ ap-∘ _ _ _ ∙ ap (ap inr) (Geq.adj b)  }
  where
    module Feq = is-equiv f-eq
    module Geq = is-equiv g-eq

⊔-emap : {i i' j j' : ULevel} {A : Type i} {A' : Type i'} {B : Type j} {B' : Type j'}
  (e : A ≃ A') (e' : B ≃ B') → (A ⊔ B ≃ A' ⊔ B')

⊔-emap {A = A} {A' = A'} {B = B} {B' = B'} e e' = (f , record { g = g ; f-g = f-g ; g-f = g-f ; adj = adj })
  where
    f : A ⊔ B → A' ⊔ B'
    f = ⊔-fmap (–> e) (–> e')

    g : A' ⊔ B' → A ⊔ B
    g = ⊔-fmap (<– e) (<– e')

    f-g : (z : A' ⊔ B') → (f (g z) == z)
    f-g (inl x) = ap inl (<–-inv-r e x)
    f-g (inr x) = ap inr (<–-inv-r e' x)

    g-f : (z : A ⊔ B) → (g (f z) == z)
    g-f (inl x) = ap inl (<–-inv-l e x)
    g-f (inr x) = ap inr (<–-inv-l e' x)

    adj : (a : A ⊔ B) → ap f (g-f a) == f-g (f a)
    adj (inl a) =
      ap f (g-f (inl a))
        =⟨ idp ⟩
      ap f (ap inl (<–-inv-l e a))
        =⟨ ∘-ap f inl _ ⟩
      ap (f ∘ inl) (<–-inv-l e a)
        =⟨ idp ⟩
      ap (inl ∘ –> e) ((<–-inv-l e a))
        =⟨ ap-∘ inl (–> e) _ ⟩
      ap inl (ap (–> e) (<–-inv-l e a))
        =⟨ ap (ap inl) (<–-inv-adj e a) ⟩
      ap inl (<–-inv-r e (–> e a))
        =⟨ idp ⟩
      f-g (f (inl a))
        =∎
    adj (inr b) =
      ap f (g-f (inr b))
        =⟨ idp ⟩
      ap f (ap inr (<–-inv-l e' b))
        =⟨ ∘-ap f inr _ ⟩
      ap (f ∘ inr) (<–-inv-l e' b)
        =⟨ idp ⟩
      ap (inr ∘ –> e') ((<–-inv-l e' b))
        =⟨ ap-∘ inr (–> e') _ ⟩
      ap inr (ap (–> e') (<–-inv-l e' b))
        =⟨ ap (ap inr) (<–-inv-adj e' b) ⟩
      ap inr (<–-inv-r e' (–> e' b))
        =⟨ idp ⟩
      f-g (f (inr b))
        =∎

⊔-cancel-l : {i j : ULevel} {A : Type i} {B : Type j} → (A ⊔ B) → (¬ A) → B
⊔-cancel-l (inl a) na = ⊥-elim (na a)
⊔-cancel-l (inr b) _ = b

⊔-cancel-r : {i j : ULevel} {A : Type i} {B : Type j} → (A ⊔ B) → (¬ B) → A
⊔-cancel-r (inl a) _ = a
⊔-cancel-r (inr b) nb = ⊥-elim (nb b)

⊔-assoc : {i j k : ULevel} {A : Type i} {B : Type j} {C : Type k} → (A ⊔ B) ⊔ C ≃ A ⊔ B ⊔ C
⊔-assoc {A = A} {B = B} {C = C} = f , record { g = g ; f-g = f-g ; g-f = g-f ; adj = adj }
  where
    f : (A ⊔ B) ⊔ C → A ⊔ B ⊔ C
    f (inl (inl x)) = inl x
    f (inl (inr x)) = inr (inl x)
    f (inr x) = inr (inr x)

    g : A ⊔ B ⊔ C → (A ⊔ B) ⊔ C
    g (inl x) = inl (inl x)
    g (inr (inl x)) = inl (inr x)
    g (inr (inr x)) = inr x

    f-g : (z : A ⊔ B ⊔ C) → (f (g z) == z)
    f-g (inl x) = idp
    f-g (inr (inl x)) = idp
    f-g (inr (inr x)) = idp

    g-f : (z : (A ⊔ B) ⊔ C) → (g (f z) == z)
    g-f (inl (inl x)) = idp
    g-f (inl (inr x)) = idp
    g-f (inr x) = idp

    adj : (a : (A ⊔ B) ⊔ C) → ap f (g-f a) == f-g (f a)
    adj (inl (inl x)) = idp
    adj (inl (inr x)) = idp
    adj (inr x) = idp

⊔-sym : {i j : ULevel} {A : Type i} {B : Type j} → (A ⊔ B) ≃ (B ⊔ A)
⊔-sym = (λ {(inl a) → inr a ; (inr b) → inl b} ) ,
  record { g = λ { (inl b) → inr b ; (inr a) → inl a}
         ; f-g = λ { (inl x) → idp ; (inr x) → idp}
         ; g-f = λ { (inl x) → idp ; (inr x) → idp}
         ; adj = λ { (inl x) → idp ; (inr x) → idp} }
