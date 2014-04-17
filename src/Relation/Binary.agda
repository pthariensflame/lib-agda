------------------------------------------------------------------------
-- The Agda standard library
--
-- Properties of homogeneous binary relations
------------------------------------------------------------------------

module Relation.Binary where

open import Data.Product
open import Data.Sum
open import Function
open import Level
import Relation.Binary.PropositionalEquality.Core as PropEq
open import Relation.Binary.Consequences
open import Relation.Binary.Core as Core using (_≡_)
import Relation.Binary.Indexed.Core as I

------------------------------------------------------------------------
-- Simple properties and equivalence relations

open Core public hiding (_≡_; refl; _≢_)

------------------------------------------------------------------------
-- Preorders

record IsPreorder {a ℓ₁ ℓ₂} {A : Set a}
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    -- Reflexivity is expressed in terms of an underlying equality:
    reflexive     : _≈_ ⇒ _∼_
    trans         : Transitive _∼_

  module Eq = IsEquivalence isEquivalence

  refl : Reflexive _∼_
  refl = reflexive Eq.refl

  ∼-resp-≈ : _∼_ Respects₂ _≈_
  ∼-resp-≈ = (λ x≈y z∼x → trans z∼x (reflexive x≈y))
           , (λ x≈y x∼z → trans (reflexive $ Eq.sym x≈y) x∼z)

record Preorder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder _≈_ _∼_

  -- A trivially indexed preorder.

  open IsPreorder isPreorder public
  open IsPreorder isPreorder using () renaming (reflexive to ∼reflexive)
  open IsEquivalence isEquivalence renaming (refl to ≈refl; sym to ≈sym; trans to ≈trans)

  indexedPreorder : ∀ {i} {I : Set i} → I.Preorder I c _ _
  indexedPreorder = record
    { Carrier = const Carrier
    ; _≈_     = _≈_
    ; _∼_     = _∼_
    ; isPreorder = record
      { isEquivalence = record
        { refl = ≈refl
        ; sym = ≈sym
        ; trans = ≈trans
        }
      ; reflexive = λ _ → ∼reflexive
      ; trans = trans
      }
    }

------------------------------------------------------------------------
-- Setoids

-- Equivalence relations are defined in Relation.Binary.Core.

record Setoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence _≈_

  open IsEquivalence isEquivalence public

  isPreorder : IsPreorder _≡_ _≈_
  isPreorder = record
    { isEquivalence = PropEq.isEquivalence
    ; reflexive     = reflexive
    ; trans         = trans
    }

  preorder : Preorder c c ℓ
  preorder = record { isPreorder = isPreorder }

  -- A trivially indexed setoid.

  indexedSetoid : ∀ {i} {I : Set i} → I.Setoid I c _
  indexedSetoid = record
    { Carrier = λ _ → Carrier
    ; _≈_     = _≈_
    ; isEquivalence = record
      { refl  = refl
      ; sym   = sym
      ; trans = trans
      }
    }

-- Ideally this would be in Level, but it can't be

Lift-setoid : ∀{aℓ a≈ℓ wℓ w≈ℓ} → Setoid aℓ a≈ℓ → Setoid (aℓ ⊔ wℓ) (a≈ℓ ⊔ w≈ℓ)
Lift-setoid {aℓ} {a≈ℓ} {wℓ} {w≈ℓ} A-setoid = record {
                                               Carrier = Lift {aℓ} {wℓ} A;
                                               _≈_ = λ {(lift x) (lift y) → Lift {a≈ℓ} {w≈ℓ} (x A≈ y)};
                                               isEquivalence =
                                                 record {
                                                 refl = λ { {lift x} → lift (A-refl {x})};
                                                 sym = λ { {lift x} {lift y} (lift p) → lift (A-sym {x} {y} p)};
                                                 trans =
                                                   λ { {lift x} {lift y} {lift z} (lift p) (lift q)
                                                        → lift (A-trans {x} {y} {z} p q)} } }
  where
    open Setoid A-setoid using () renaming ( Carrier to A ; _≈_ to _A≈_ ; refl to A-refl ; sym to A-sym ; trans to A-trans )

------------------------------------------------------------------------
-- Decidable equivalence relations

record IsDecEquivalence {a ℓ} {A : Set a}
                        (_≈_ : Rel A ℓ) : Set (a ⊔ ℓ) where
  infix 4 _≟_
  field
    isEquivalence : IsEquivalence _≈_
    _≟_           : Decidable _≈_

  open IsEquivalence isEquivalence public

record DecSetoid c ℓ : Set (suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier          : Set c
    _≈_              : Rel Carrier ℓ
    isDecEquivalence : IsDecEquivalence _≈_

  open IsDecEquivalence isDecEquivalence public

  setoid : Setoid c ℓ
  setoid = record { isEquivalence = isEquivalence }

  open Setoid setoid public using (preorder; indexedSetoid)

------------------------------------------------------------------------
-- Partial orders

record IsPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                      (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                      Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder _≈_ _≤_
    antisym    : Antisymmetric _≈_ _≤_

  open IsPreorder isPreorder public
         renaming (∼-resp-≈ to ≤-resp-≈)

record Poset c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier        : Set c
    _≈_            : Rel Carrier ℓ₁
    _≤_            : Rel Carrier ℓ₂
    isPartialOrder : IsPartialOrder _≈_ _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }
  
  indexedPoset : ∀ {i} {I : Set i} → I.Poset I c _ _
  indexedPoset = record
    { Carrier = λ _ → Carrier
    ; _≈_ = _≈_
    ; _≤_ = _≤_
    ; isPartialOrder = record
      { isPreorder = I.Preorder.isPreorder (Preorder.indexedPreorder preorder)
      ; antisym = antisym
      }
    }

------------------------------------------------------------------------
-- Decidable partial orders

record IsDecPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                         (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                         Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    _≟_            : Decidable _≈_
    _≤?_           : Decidable _≤_

  private
    module PO = IsPartialOrder isPartialOrder
  open PO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = PO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public

record DecPoset c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier           : Set c
    _≈_               : Rel Carrier ℓ₁
    _≤_               : Rel Carrier ℓ₂
    isDecPartialOrder : IsDecPartialOrder _≈_ _≤_

  private
    module DPO = IsDecPartialOrder isDecPartialOrder
  open DPO public hiding (module Eq)

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record { isDecEquivalence = DPO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public

------------------------------------------------------------------------
-- Strict partial orders

record IsStrictPartialOrder {a ℓ₁ ℓ₂} {A : Set a}
                            (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) :
                            Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    irrefl        : Irreflexive _≈_ _<_
    trans         : Transitive _<_
    <-resp-≈      : _<_ Respects₂ _≈_

  module Eq = IsEquivalence isEquivalence

record StrictPartialOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier              : Set c
    _≈_                  : Rel Carrier ℓ₁
    _<_                  : Rel Carrier ℓ₂
    isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_

  open IsStrictPartialOrder isStrictPartialOrder public

------------------------------------------------------------------------
-- Total orders

record IsTotalOrder {a ℓ₁ ℓ₂} {A : Set a}
                    (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                    Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPartialOrder : IsPartialOrder _≈_ _≤_
    total          : Total _≤_

  open IsPartialOrder isPartialOrder public

record TotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier      : Set c
    _≈_          : Rel Carrier ℓ₁
    _≤_          : Rel Carrier ℓ₂
    isTotalOrder : IsTotalOrder _≈_ _≤_

  open IsTotalOrder isTotalOrder public

  poset : Poset c ℓ₁ ℓ₂
  poset = record { isPartialOrder = isPartialOrder }

  open Poset poset public using (preorder)

------------------------------------------------------------------------
-- Decidable total orders

record IsDecTotalOrder {a ℓ₁ ℓ₂} {A : Set a}
                       (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                       Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  infix 4 _≟_ _≤?_
  field
    isTotalOrder : IsTotalOrder _≈_ _≤_
    _≟_          : Decidable _≈_
    _≤?_         : Decidable _≤_

  private
    module TO = IsTotalOrder isTotalOrder
  open TO public hiding (module Eq)

  module Eq where

    isDecEquivalence : IsDecEquivalence _≈_
    isDecEquivalence = record
      { isEquivalence = TO.isEquivalence
      ; _≟_           = _≟_
      }

    open IsDecEquivalence isDecEquivalence public

record DecTotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier         : Set c
    _≈_             : Rel Carrier ℓ₁
    _≤_             : Rel Carrier ℓ₂
    isDecTotalOrder : IsDecTotalOrder _≈_ _≤_

  private
    module DTO = IsDecTotalOrder isDecTotalOrder
  open DTO public hiding (module Eq)

  totalOrder : TotalOrder c ℓ₁ ℓ₂
  totalOrder = record { isTotalOrder = isTotalOrder }

  open TotalOrder totalOrder public using (poset; preorder)

  module Eq where

    decSetoid : DecSetoid c ℓ₁
    decSetoid = record { isDecEquivalence = DTO.Eq.isDecEquivalence }

    open DecSetoid decSetoid public

------------------------------------------------------------------------
-- Strict total orders

-- Note that these orders are decidable (see compare).

record IsStrictTotalOrder {a ℓ₁ ℓ₂} {A : Set a}
                          (_≈_ : Rel A ℓ₁) (_<_ : Rel A ℓ₂) :
                          Set (a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence _≈_
    trans         : Transitive _<_
    compare       : Trichotomous _≈_ _<_
    <-resp-≈      : _<_ Respects₂ _≈_

  infix 4 _≟_ _<?_

  _≟_ : Decidable _≈_
  _≟_ = tri⟶dec≈ compare

  _<?_ : Decidable _<_
  _<?_ = tri⟶dec< compare

  isDecEquivalence : IsDecEquivalence _≈_
  isDecEquivalence = record
    { isEquivalence = isEquivalence
    ; _≟_           = _≟_
    }

  module Eq = IsDecEquivalence isDecEquivalence

  isStrictPartialOrder : IsStrictPartialOrder _≈_ _<_
  isStrictPartialOrder = record
    { isEquivalence = isEquivalence
    ; irrefl        = tri⟶irr <-resp-≈ Eq.sym compare
    ; trans         = trans
    ; <-resp-≈      = <-resp-≈
    }

  open IsStrictPartialOrder isStrictPartialOrder public using (irrefl)

record StrictTotalOrder c ℓ₁ ℓ₂ : Set (suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _<_
  field
    Carrier            : Set c
    _≈_                : Rel Carrier ℓ₁
    _<_                : Rel Carrier ℓ₂
    isStrictTotalOrder : IsStrictTotalOrder _≈_ _<_

  open IsStrictTotalOrder isStrictTotalOrder public
    hiding (module Eq)

  strictPartialOrder : StrictPartialOrder c ℓ₁ ℓ₂
  strictPartialOrder =
    record { isStrictPartialOrder = isStrictPartialOrder }

  decSetoid : DecSetoid c ℓ₁
  decSetoid = record { isDecEquivalence = isDecEquivalence }

  module Eq = DecSetoid decSetoid
