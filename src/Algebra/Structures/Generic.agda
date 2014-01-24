------------------------------------------------------------------------
-- The Agda standard library
--
-- A generic framework for algebraic structures
------------------------------------------------------------------------

module Algebra.Structures.Generic where
open import Function.Equality renaming ( setoid to Π-setoid ; _⇨_ to _⟶-setoid_ ; ≡-setoid to Π-≡-setoid )
open import Function.Equivalence renaming ( setoid to Equivalence-setoid )
open import Data.Nat renaming ( _⊔_ to _max_ ; _⊓_ to _min_  ; _≟_ to _≟-ℕ_ )
open import Data.Fin renaming ( _+_ to _Fin+_ )
open import Data.Bool renaming ( _≟_ to _≟-Bool_ )
open import Data.Vec
open import Level renaming ( zero to ℓzero ; suc to ℓsuc ; lift to ℓlift )
open import Relation.Binary hiding ( REL ; Rel )
open import Relation.Binary.PropositionalEquality renaming ( setoid to ≡-setoid )
open import Relation.Nullary
open import Data.List.Unique

mutual
  infixl 1 _withOp_requiring_ _withRel_requiring_ _withLaw_requiring_
  data Descriptor : (nOps : ℕ) (nRels : ℕ) (nLaws : ℕ) → Set where
    emptySpec : Descriptor 0 0 0
    _withOp_requiring_ : {nOps : ℕ} {nRels : ℕ} {nLaws : ℕ} (spec : Descriptor nOps nRels nLaws) (n : ℕ)
                         (reqs : UList (≡-setoid (EquationSpec spec))) → Descriptor (suc nOps) nRels nLaws
    _withRel_requiring_ : {nOps : ℕ} {nRels : ℕ} {nLaws : ℕ} (spec : Descriptor nOps nRels nLaws) (n : ℕ)
                          (reqs : UList (≡-setoid (EquationSpec spec)))→ Descriptor nOps (suc nRels) nLaws
    _withLaw_requiring_ : {nOps : ℕ} {nRels : ℕ} {nLaws : ℕ} (spec : Descriptor nOps nRels nLaws) (lawSpec : EquationSpec spec)
                          (reqs : UList (≡-setoid (EquationSpec spec))) → Descriptor nOps nRels (suc nLaws)
  
  opArity : {nOps : ℕ} {nRels : ℕ} {nLaws : ℕ} (spec : Descriptor nOps nRels nLaws) (opId : Fin nOps) → ℕ
  opArity emptySpec ()
  opArity (spec withOp n requiring _) zero = n
  opArity (spec withOp _ requiring _) (suc opId) = opArity spec opId
  opArity (spec withRel _ requiring _) opId = opArity spec opId
  opArity (spec withLaw _ requiring _) opId = opArity spec opId
  
  relArity : {nOps : ℕ} {nRels : ℕ} {nLaws : ℕ} (spec : Descriptor nOps nRels nLaws) (relId : Fin nRels) → ℕ
  relArity emptySpec ()
  relArity (spec withOp _ requiring _) relId = relArity spec relId
  relArity (spec withRel n requiring _) zero = n
  relArity (spec withRel _ requiring _) (suc relId) = relArity spec relId
  relArity (spec withLaw _ requiring _) relId = relArity spec relId
  
  infixl 3 apply_to_
  record ExpressionSpec {nOps : ℕ} {nRels : ℕ} {nLaws : ℕ} (spec : Descriptor nOps nRels nLaws) : Set where
    constructor apply_to_
    field
      opId : Fin nOps
      operandSpecs : Vec (ExpressionSpec spec) (opArity spec opId)
  
  infix 2 _relates_
  record EquationSpec {nOps : ℕ} {nRels : ℕ} {nLaws : ℕ} (spec : Descriptor nOps nRels nLaws) : Set where
    constructor _relates_
    field
      relId : Fin nRels
      expressionSpecs : Vec (ExpressionSpec spec) (relArity spec relId)

open ExpressionSpec public
open EquationSpec public

private
  BareOp : ∀{sℓ} (Carrier : Set sℓ) (opId : ℕ) → Set sℓ
  BareOp Carrier zero = Carrier
  BareOp Carrier (suc opId) = Carrier → BareOp Carrier opId
  
  BareOp-setoid : ∀{sℓ s≈ℓ} (Carrier : Setoid sℓ s≈ℓ) (opId : ℕ) → Setoid (sℓ ⊔ s≈ℓ) (sℓ ⊔ s≈ℓ)
  BareOp-setoid {sℓ} {s≈ℓ} Carrier zero = Lift-setoid {sℓ} {s≈ℓ} {s≈ℓ} {sℓ} Carrier
  BareOp-setoid Carrier (suc opId) = Carrier ⟶-setoid BareOp-setoid Carrier opId
  
  BareRel : ∀{sℓ} (Carrier : Set sℓ) (srℓ : Level) (relId : ℕ) → Set (sℓ ⊔ ℓsuc srℓ)
  BareRel {sℓ} Carrier srℓ zero = Lift {ℓsuc srℓ} {sℓ} (Set srℓ)
  BareRel Carrier srℓ (suc relId) = Carrier → BareRel Carrier srℓ relId
  
  BareRel-setoid : ∀{sℓ s≈ℓ} (Carrier : Setoid sℓ s≈ℓ) (srℓ : Level) (relId : ℕ) → Setoid (sℓ ⊔ s≈ℓ ⊔ ℓsuc srℓ) (sℓ ⊔ s≈ℓ ⊔ srℓ)
  BareRel-setoid {sℓ} {s≈ℓ} Carrier srℓ zero = Lift-setoid {ℓsuc srℓ} {srℓ} {sℓ ⊔ s≈ℓ} {sℓ ⊔ s≈ℓ} (⇔-setoid srℓ)
  BareRel-setoid Carrier srℓ (suc relId) = Carrier ⟶-setoid BareRel-setoid Carrier srℓ relId
