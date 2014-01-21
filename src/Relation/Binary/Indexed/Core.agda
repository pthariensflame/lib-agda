------------------------------------------------------------------------
-- The Agda standard library
--
-- Indexed binary relations
------------------------------------------------------------------------

-- This file contains some core definitions which are reexported by
-- Relation.Binary.Indexed.

module Relation.Binary.Indexed.Core where

open import Function
open import Level
open import Data.Product
import Relation.Binary.Core as B
import Relation.Binary.Core as P
import Relation.Binary.PropositionalEquality.Core as PropEq
import Relation.Binary.HeterogeneousEquality.Core as HeteroEq

------------------------------------------------------------------------
-- Indexed binary relations

-- Heterogeneous.

REL : ∀ {i₁ i₂ a₁ a₂} {I₁ : Set i₁} {I₂ : Set i₂} →
      (I₁ → Set a₁) → (I₂ → Set a₂) → (ℓ : Level) → Set _
REL A₁ A₂ ℓ = ∀ {i₁ i₂} → A₁ i₁ → A₂ i₂ → Set ℓ

-- Homogeneous.

Rel : ∀ {i a} {I : Set i} → (I → Set a) → (ℓ : Level) → Set _
Rel A ℓ = REL A A ℓ

------------------------------------------------------------------------
-- Simple properties of indexed binary relations

-- Reflexivity.

Reflexive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Reflexive _ _∼_ = ∀ {i} → B.Reflexive (_∼_ {i})

-- Symmetry.

Symmetric : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Symmetric _ _∼_ = ∀ {i j} → B.Sym (_∼_ {i} {j}) _∼_

-- Antisymmetric

Antisymmetric : ∀ {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a) → Rel A ℓ₁ → Rel A ℓ₂ → Set _
Antisymmetric A _≈_ _≤_ = ∀ {i j} {x : A i} {y : A j} → x ≤ y → y ≤ x → x ≈ y

-- Transitivity.

Transitive : ∀ {i a ℓ} {I : Set i} (A : I → Set a) → Rel A ℓ → Set _
Transitive _ _∼_ = ∀ {i j k} → B.Trans _∼_ (_∼_ {j}) (_∼_ {i} {k})

------------------------------------------------------------------------
-- Setoids, preorders, and partial orders

record IsEquivalence {i a ℓ} {I : Set i} (A : I → Set a)
                     (_≈_ : Rel A ℓ) : Set (i ⊔ a ⊔ ℓ) where
  field
    refl  : Reflexive A _≈_
    sym   : Symmetric A _≈_
    trans : Transitive A _≈_

  reflexive : ∀ {ix ix′} {x : A ix} {y : A ix′} → (P._≡_ ix ix′) → (HeteroEq._≅_ x y) → (x ≈ y)
  reflexive P.refl HeteroEq.refl = refl

record IsPreorder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                  (_≈_ : Rel A ℓ₁) -- The underlying equality.
                  (_∼_ : Rel A ℓ₂) -- The relation.
                  : Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isEquivalence : IsEquivalence A _≈_
    -- Reflexivity is expressed in terms of an underlying equality:
    reflexive     : ∀ {ix ix′} {x : A ix} {y : A ix′} → (P._≡_ ix ix′) → x ≈ y → x ∼ y
    trans         : Transitive A _∼_

  module Eq = IsEquivalence isEquivalence

  refl : Reflexive A _∼_
  refl {i = i} = reflexive P.refl Eq.refl

  ∼-resp-≈ : (∀ {ix ix′} {x : A ix} {x′ y′ : A ix′} → x′ ≈ y′ → x ∼ x′ → x ∼ y′) × (∀ {ix ix′} {y : A ix′} {x′ y′ : A ix} → x′ ≈ y′ → x′ ∼ y → y′ ∼ y)
  ∼-resp-≈ = (λ x≈y z∼x → trans z∼x (reflexive B.refl x≈y))
           , (λ x≈y x∼z → trans (reflexive B.refl $ Eq.sym x≈y) x∼z)

record Preorder {i} (I : Set i) c ℓ₁ ℓ₂ : Set (i ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _∼_
  field
    Carrier    : I → Set c
    _≈_        : Rel Carrier ℓ₁  -- The underlying equality.
    _∼_        : Rel Carrier ℓ₂  -- The relation.
    isPreorder : IsPreorder {I = I} Carrier _≈_ _∼_

  open IsPreorder isPreorder public

record Setoid {i} (I : Set i) c ℓ : Set (i ⊔ suc (c ⊔ ℓ)) where
  infix 4 _≈_
  field
    Carrier       : I → Set c
    _≈_           : Rel Carrier ℓ
    isEquivalence : IsEquivalence Carrier _≈_

  open IsEquivalence isEquivalence public

  isPreorder : IsPreorder {i} {c} {c} {ℓ} {I = I} Carrier (λ a₁ a₂ → Lift (HeteroEq._≅_ a₁ a₂)) _≈_
  isPreorder = record
    { isEquivalence = record
      { refl  = lift HeteroEq.refl
      ; sym   = lift ∘′ HeteroEq.sym ∘′ lower
      ; trans = λ {(lift x) (lift y) → lift (HeteroEq.trans x y)}
      }
    ; reflexive     = λ { {ix} {.ix} {x} {.x} P.refl (lift HeteroEq.refl) → refl}
    ; trans         = trans
    }
  
  module PO = IsPreorder isPreorder

  preorder : Preorder I c c ℓ
  preorder = record
    { isPreorder = record
      { isEquivalence = PO.isEquivalence
      ; reflexive = PO.reflexive
      ; trans = PO.trans
      }
    }

------------------------------------------------------------------------
-- Partial orders

record IsPartialOrder {i a ℓ₁ ℓ₂} {I : Set i} (A : I → Set a)
                      (_≈_ : Rel A ℓ₁) (_≤_ : Rel A ℓ₂) :
                      Set (i ⊔ a ⊔ ℓ₁ ⊔ ℓ₂) where
  field
    isPreorder : IsPreorder A _≈_ _≤_
    antisym    : Antisymmetric A _≈_ _≤_

  open IsPreorder isPreorder public
         renaming (∼-resp-≈ to ≤-resp-≈)

record Poset {i} (I : Set i) c ℓ₁ ℓ₂ : Set (i ⊔ suc (c ⊔ ℓ₁ ⊔ ℓ₂)) where
  infix 4 _≈_ _≤_
  field
    Carrier        : I → Set c
    _≈_            : Rel Carrier ℓ₁
    _≤_            : Rel Carrier ℓ₂
    isPartialOrder : IsPartialOrder Carrier _≈_ _≤_

  open IsPartialOrder isPartialOrder public

  preorder : Preorder I c ℓ₁ ℓ₂
  preorder = record { isPreorder = isPreorder }
