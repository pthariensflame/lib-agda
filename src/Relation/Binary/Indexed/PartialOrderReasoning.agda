------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using an indexed partial order
------------------------------------------------------------------------

open import Relation.Binary.Indexed

module Relation.Binary.Indexed.PartialOrderReasoning
         {i} {I : Set i} {p₁ p₂ p₃} (P : Poset I p₁ p₂ p₃) where

open Poset P
import Relation.Binary.Indexed.PreorderReasoning as PreR
open PreR preorder public renaming (_∼⟨_⟩_ to _≤⟨_⟩_)
