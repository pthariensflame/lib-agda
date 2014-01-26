------------------------------------------------------------------------
-- The Agda standard library
--
-- Operations on nullary relations (like negation and decidability)
------------------------------------------------------------------------

-- Some operations on/properties of nullary relations, i.e. sets.

module Relation.Nullary where

import Relation.Nullary.Core as Core

------------------------------------------------------------------------
-- Negation

open Core public using (¬_)

infix 3 ¬-_

¬-_ : ∀ {a b ℓ} {A : Set a} {B : Set b} → (A → B → Set ℓ) → (A → B → Set ℓ)
(¬- f) x y = ¬ f x y

------------------------------------------------------------------------
-- Decidable relations

open Core public using (Dec; yes; no)
