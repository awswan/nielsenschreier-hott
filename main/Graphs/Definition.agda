{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Basics
open import lib.types.Bool

module Graphs.Definition where

{- A graph consists of types of Edges and Vertices together with two endpoint maps. We
   often just talk about the types and the endpoint maps are clear from the context
   (i.e. derived by instance resolution). -}
record Graph {i j : ULevel} (E : Type i) (V : Type j) : Type (lmax i j) where
  constructor graph
  field
    π₀ : E → V
    π₁ : E → V

open Graph ⦃...⦄ public -- see agda documentation on instance arguments
