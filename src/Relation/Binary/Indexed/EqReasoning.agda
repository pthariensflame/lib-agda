------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for indexed equational reasoning
------------------------------------------------------------------------

open import Relation.Binary.Indexed

module Relation.Binary.Indexed.EqReasoning {i s₁ s₂} {I : Set i} (S : Setoid I s₁ s₂) where

open Setoid S
import Relation.Binary.Indexed.PreorderReasoning as PreR
open PreR preorder public
       renaming ( _∼⟨_⟩_  to _≈⟨_⟩_
                ; _≈⟨_⟩_  to _≅⟨_⟩_
                ; _≈⟨⟩_  to _≅⟨⟩_
                )
