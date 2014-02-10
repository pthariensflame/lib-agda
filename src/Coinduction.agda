------------------------------------------------------------------------
-- The Agda standard library
--
-- Basic types related to coinduction, and some properties of them
------------------------------------------------------------------------

module Coinduction where

open import Level
open import Category.Monad
open import Relation.Binary
open import Relation.Binary.PropositionalEquality hiding (preorder; setoid)

-- just a convenient way to section out the universe level
module _ {a} where

------------------------------------------------------------------------
-- A type used to make recursive arguments coinductive

  infix 1000 ♯_

  postulate
    ∞  : (A : Set a) → Set a
    ♯_ : {A : Set a} → A → ∞ A
    ♭  : {A : Set a} → ∞ A → A

{-# BUILTIN INFINITY ∞  #-}
{-# BUILTIN SHARP    ♯_ #-}
{-# BUILTIN FLAT     ♭  #-}

-- just a convenient way to section out the universe level (again)
module _ {a} where

  monad : RawMonad (∞ {a})
  monad = record
    { return = ♯_
    ; _>>=_  = λ x f → ♯ ♭ (f (♭ x))
    }

  open RawMonad monad public

------------------------------------------------------------------------
-- A coinductive adaptation of propositional equality
  
  infix 1000 ♯≡_

  record _∞≡_ {A : Set a} (x : ∞ A) (y : ∞ A) : Set a where
    constructor ♯≡_
    field
      ♭≡ : ∞ (♭ x ≡ ♭ y)

  open _∞≡_ public

  infix 1000 ♯≡′_

  ♯≡′_ : {A : Set a} {x : ∞ A} {y : ∞ A} → ♭ x ≡ ♭ y → x ∞≡ y
  ♯≡′_ p = ♯≡ ♯ p
  
  ♭≡′ : {A : Set a} {x : ∞ A} {y : ∞ A} → x ∞≡ y → ♭ x ≡ ♭ y
  ♭≡′ p = ♭ (♭≡ p)

  setoid : (A : Set a) → Setoid _ _
  setoid A = record
    { Carrier       = ∞ A
    ; _≈_           = _∞≡_
    ; isEquivalence = record
      { refl          = ♯≡′ refl
      ; sym           = λ p → ♯≡′ sym (♭ (♭≡ p))
      ; trans         = λ pₗ pᵣ → ♯≡′ trans (♭≡′ pₗ) (♭≡′ pᵣ)
      }
    }

  module _ {A : Set a} where
    open Setoid (setoid A) public using (preorder) renaming (refl to ∞refl ; reflexive to ∞reflexive ; sym to ∞sym ; trans to ∞trans )

------------------------------------------------------------------------
-- Rec, a type which is analogous to the Rec type constructor used in
-- (the current version of) ΠΣ

  data Rec (A : ∞ (Set a)) : Set a where
    fold : (x : ♭ A) → Rec A

  unfold : {A : ∞ (Set a)} → Rec A → ♭ A
  unfold (fold x) = x

{-

  -- If --guardedness-preserving-type-constructors is enabled one can
  -- define types like ℕ by recursion:

  open import Data.Sum
  open import Data.Unit

  ℕ : Set
  ℕ = ⊤ ⊎ Rec (♯ ℕ)

  zero : ℕ
  zero = inj₁ _

  suc : ℕ → ℕ
  suc n = inj₂ (fold n)

  ℕ-rec : (P : ℕ → Set) →
          P zero →
          (∀ n → P n → P (suc n)) →
          ∀ n → P n
  ℕ-rec P z s (inj₁ _)        = z
  ℕ-rec P z s (inj₂ (fold n)) = s n (ℕ-rec P z s n)

  -- This feature is very experimental, though: it may lead to
  -- inconsistencies.

-}
