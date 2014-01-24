------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists with a built-in element uniqueness system (ordered subsets of a setoid)
------------------------------------------------------------------------

module Data.List.Unique where
open import Level renaming ( zero to ℓzero ; suc to ℓsuc ; lift to ℓlift )
open import Function
open import Data.Nat renaming ( _≟_ to _≟-ℕ_ ; _⊔_ to _max_ ; _⊓_ to _min_ )
open import Relation.Binary
open import Relation.Nullary

mutual
  
  data UList {eℓ e≈ℓ} (Elem : Setoid eℓ e≈ℓ) : Set (eℓ ⊔ e≈ℓ) where
    [] : UList Elem
    _∷_uniq_ : (x : Setoid.Carrier Elem) → (xs : UList Elem) → x ∉ xs → UList Elem
  
  data All {eℓ e≈ℓ rℓ} {Elem : Setoid eℓ e≈ℓ} (P : Setoid.Carrier Elem → Set rℓ) : (xs : UList Elem) → Set (eℓ ⊔ e≈ℓ ⊔ rℓ) where
    [] : All P []
    _∷_uniq_ : ∀{x xs} → P x → All P xs → ∀ p → All P (x ∷ xs uniq p)
  
  data _∉_ {eℓ e≈ℓ} {Elem : Setoid eℓ e≈ℓ} (v : Setoid.Carrier Elem) : (xs : UList Elem) → Set (eℓ ⊔ e≈ℓ) where
    [] : v ∉ []
    _∷_uniq_ : ∀{x xs} → All (¬_ ∘′ Setoid._≈_ Elem x) xs → v ∉ xs → ∀ p → v ∉ (x ∷ xs uniq p)

data Any {eℓ e≈ℓ rℓ} {Elem : Setoid eℓ e≈ℓ} (P : Setoid.Carrier Elem → Set rℓ) : (xs : UList Elem) → Set (eℓ ⊔ e≈ℓ ⊔ rℓ) where
  hereIn_∷_uniq_ : ∀{x} → P x → ∀ xs p → Any P (x ∷ xs uniq p)
  thereIn_∷_uniq_ : ∀ x {xs} → Any P xs → ∀ p → Any P (x ∷ xs uniq p)

length : ∀{eℓ e≈ℓ} {Elem : Setoid eℓ e≈ℓ} → UList Elem → ℕ
length [] = 0
length (_ ∷ xs uniq _) = suc (length xs)
