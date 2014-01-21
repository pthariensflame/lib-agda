------------------------------------------------------------------------
-- The Agda standard library
--
-- Complex graphs
------------------------------------------------------------------------

module Data.Graph where
open import Level renaming ( zero to ℓzero ; suc to ℓsuc ; lift to ℓlift )
open import Function
open import Induction
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Maybe
open import Data.Nat renaming ( _⊔_ to _max_ ; _⊓_ to _min_ )
open import Data.Fin
open import Algebra
open import Relation.Binary
open import Relation.Unary
open import Relation.Nullary

record Graph {nn nd en ed} (NodeName : Set nn) (NodeData : NodeName → Set nd) (EdgeName : NodeName → NodeName → Set en) (EdgeData : {start : NodeName} → {end : NodeName} → EdgeName start end → Set ed) : Set (nn ⊔ nd ⊔ en ⊔ ed) where
  constructor graphWithNodes_andEdges_
  field
    nodeData : (name : NodeName) → NodeData name
    edgeData : {start : NodeName} → {end : NodeName} → (name : EdgeName start end) → EdgeData {start} {end} name

simpleCompleteGraphWithNodes_ : ∀{nn nd} {NodeName : Set nn} {NodeData : NodeName → Set nd} → ((name : NodeName) → NodeData name) → Graph NodeName NodeData (λ _ _ → ⊤) (λ _ → ⊤)
simpleCompleteGraphWithNodes nodeSpec = graphWithNodes nodeSpec andEdges λ _ → tt
