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
open import Data.Vec
open import Level renaming ( zero to ℓzero ; suc to ℓsuc ; lift to ℓlift )
open import Relation.Binary hiding ( REL ; Rel )
open import Relation.Binary.PropositionalEquality renaming ( setoid to ≡-setoid )
open import Relation.Nullary
open import Reflection renaming ( _≟_ to _≟-Term_ )
import Relation.Binary.Reflection as RBR

module Primitive where

  infixl 1 addOp_to_
  data OpsSpec : (nOps : ℕ) → Set where
    emptyOpsSpec : OpsSpec 0
    addOp_to_ : (n : ℕ) → {nOps : ℕ} → OpsSpec nOps → OpsSpec (suc nOps)

  opArity : {nOps : ℕ} → (Ops : OpsSpec nOps) → (opId : Fin nOps) → ℕ
  opArity emptyOpsSpec ()
  opArity (addOp n to _) zero = n
  opArity (addOp _ to Ops) (suc opId) = opArity Ops opId
  
  infixl 1 addRel_to_
  data RelsSpec : (nRels : ℕ) → Set where
    emptyRelsSpec : RelsSpec 0
    addRel_to_ : (n : ℕ) → {nRels : ℕ} → RelsSpec nRels → RelsSpec (suc nRels)

  relArity : {nRels : ℕ} → (Rels : RelsSpec nRels) → (relId : Fin nRels) → ℕ
  relArity emptyRelsSpec ()
  relArity (addRel n to _) zero = n
  relArity (addRel _ to Rels) (suc relId) = relArity Rels relId
  
  mutual
    infixl 3 apply_to_
    record ExpressionSpec {nOps : ℕ} (Ops : OpsSpec nOps) : Set where
      constructor apply_to_
      field
        opId : Fin nOps
        operandSpecs : Vec (ExpressionSpec Ops) (opArity Ops opId)

  open ExpressionSpec public
  
  infix 2 _relates_
  record EquationSpec {nOps : ℕ} (Ops : OpsSpec nOps) {nRels : ℕ} (Rels : RelsSpec nRels) : Set where
    constructor _relates_
    field
      relId : Fin nRels
      expressionSpecs : Vec (ExpressionSpec Ops) (relArity Rels relId)

  open EquationSpec public
  
  infixl 1 addLaw_to_
  data LawsSpec {nOps : ℕ} (Ops : OpsSpec nOps) {nRels : ℕ} (Rels : RelsSpec nRels) : (nLaws : ℕ) → Set where
    emptyLawsSpec : LawsSpec Ops Rels 0
    addLaw_to_ : (lawSpec : EquationSpec Ops Rels) → {nLaws : ℕ} → LawsSpec Ops Rels nLaws → LawsSpec Ops Rels (suc nLaws)

open Primitive

Op : ∀{sℓ} (Carrier : Set sℓ) (n : ℕ) → Set sℓ
Op Carrier zero = Carrier
Op Carrier (suc n) = Carrier → Op Carrier n

Op-setoid : ∀{sℓ s≈ℓ} (Carrier : Setoid sℓ s≈ℓ) (n : ℕ) → Setoid (sℓ ⊔ s≈ℓ) (sℓ ⊔ s≈ℓ)
Op-setoid {sℓ} {s≈ℓ} Carrier zero = Lift-setoid {sℓ} {s≈ℓ} {s≈ℓ} {sℓ} Carrier
Op-setoid Carrier (suc n) = Carrier ⟶-setoid Op-setoid Carrier n

Rel : ∀{sℓ} (Carrier : Set sℓ) (srℓ : Level) (n : ℕ) → Set (sℓ ⊔ ℓsuc srℓ)
Rel {sℓ} Carrier srℓ zero = Lift {ℓsuc srℓ} {sℓ} (Set srℓ)
Rel Carrier srℓ (suc n) = Carrier → Rel Carrier srℓ n

Rel-setoid : ∀{sℓ s≈ℓ} (Carrier : Setoid sℓ s≈ℓ) (srℓ : Level) (n : ℕ) → Setoid (sℓ ⊔ s≈ℓ ⊔ ℓsuc srℓ) (sℓ ⊔ s≈ℓ ⊔ srℓ)
Rel-setoid {sℓ} {s≈ℓ} Carrier srℓ zero = Lift-setoid {ℓsuc srℓ} {srℓ} {sℓ ⊔ s≈ℓ} {sℓ ⊔ s≈ℓ} (⇔-setoid srℓ)
Rel-setoid Carrier srℓ (suc n) = Carrier ⟶-setoid Rel-setoid Carrier srℓ n
