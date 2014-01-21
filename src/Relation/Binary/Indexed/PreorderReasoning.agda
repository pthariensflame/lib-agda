------------------------------------------------------------------------
-- The Agda standard library
--
-- Convenient syntax for "equational reasoning" using an indexed preorder
------------------------------------------------------------------------

open import Relation.Binary.Indexed
import Relation.Binary.Core as P

module Relation.Binary.Indexed.PreorderReasoning
         {ℓ} {I : Set ℓ} {p₁ p₂ p₃} (P : Preorder I p₁ p₂ p₃) where

open Preorder P

infix  4 _IsRelatedTo_
infix  2 _∎
infixr 2 _∼⟨_⟩_ _≈⟨_⟩_ _≈⟨⟩_
infix  1 begin_

-- This seemingly unnecessary type is used to make it possible to
-- infer arguments even if the underlying equality evaluates.

data _IsRelatedTo_ {i} {j} (x : Carrier i) (y : Carrier j) : Set p₃ where
  relTo : (x∼y : x ∼ y) → x IsRelatedTo y

begin_ : ∀ {i j} {x : Carrier i} {y : Carrier j} → x IsRelatedTo y → x ∼ y
begin relTo x∼y = x∼y

_∼⟨_⟩_ : ∀ {i j k} (x : Carrier i) {y : Carrier j} {z : Carrier k} → x ∼ y → y IsRelatedTo z → x IsRelatedTo z
_ ∼⟨ x∼y ⟩ relTo y∼z = relTo (trans x∼y y∼z)

_≈⟨_⟩_ : ∀ {i j} (x : Carrier i) {y : Carrier i} {z : Carrier j} → x ≈ y → y IsRelatedTo z → x IsRelatedTo z
_ ≈⟨ x≈y ⟩ relTo y∼z = relTo (trans (reflexive P.refl x≈y) y∼z)

_≈⟨⟩_ : ∀ {i j} (x : Carrier i) {y : Carrier j} → x IsRelatedTo y → x IsRelatedTo y
_ ≈⟨⟩ x∼y = x∼y

_∎ : ∀ {i} (x : Carrier i) → x IsRelatedTo x
_∎ _ = relTo refl
