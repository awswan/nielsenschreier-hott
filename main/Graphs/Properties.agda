{-# OPTIONS --without-K --exact-split --rewriting #-}

open import lib.Basics
open import lib.NConnected

open import Graphs.Definition
open import Coequalizers.Definition

{- We will consider two properties of graphs: if they are trees and if they are connected,
   both are defined in terms of the geometric realisation (coequalizer). -}
module Graphs.Properties where

{- A graph is a tree if its coequalizer is contractible. -}
is-tree : {i j : ULevel} {E : Type i} {V : Type j} ( gph : Graph E V ) → Type (lmax i j)
is-tree gph = is-contr (Coeq gph)

{- A graph is connected if its coequalizer is connected. -}
gph-is-connected : {i j : ULevel} {E : Type i} {V : Type j} (gph : Graph E V) → Type (lmax i j)
gph-is-connected gph = is-connected 0 (Coeq gph)
