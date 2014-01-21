------------------------------------------------------------------------
-- The Agda standard library
--
-- Some unit types
------------------------------------------------------------------------

module Data.Unit where

open import Level
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality as PropEq
  using (_≡_; refl)

-- Some types and operations are defined in Data.Unit.Core.

open import Data.Unit.Core public

------------------------------------------------------------------------
-- A unit type defined as a record type

-- Note that the name of this type is "\top", not T.

record ⊤ : Set where
  constructor tt

record _≤_ (x y : ⊤) : Set where
  constructor tt≤tt

------------------------------------------------------------------------
-- Operations

_≟_ : Decidable {A = ⊤} _≡_
_ ≟ _ = yes refl

_≤?_ : Decidable {A = ⊤} _≤_
_ ≤? _ = yes tt≤tt

total : Total _≤_
total _ _ = inj₁ tt≤tt

------------------------------------------------------------------------
-- Properties

preorder : Preorder zero zero zero
preorder = PropEq.preorder ⊤

setoid : Setoid zero zero
setoid = PropEq.setoid ⊤

decTotalOrder : DecTotalOrder zero zero zero
decTotalOrder = record
  { Carrier         = ⊤
  ; _≈_             = _≡_
  ; _≤_             = _≤_
  ; isDecTotalOrder = record
      { isTotalOrder = record
          { isPartialOrder = record
              { isPreorder = record
                  { isEquivalence = PropEq.isEquivalence
                  ; reflexive     = λ _ → tt≤tt
                  ; trans         = λ _ _ → tt≤tt
                  }
              ; antisym  = antisym
              }
          ; total = total
          }
      ; _≟_  = _≟_
      ; _≤?_ = _≤?_
      }
  }
  where
  antisym : Antisymmetric _≡_ _≤_
  antisym _ _ = refl

decSetoid : DecSetoid zero zero
decSetoid = DecTotalOrder.Eq.decSetoid decTotalOrder

poset : Poset zero zero zero
poset = DecTotalOrder.poset decTotalOrder
