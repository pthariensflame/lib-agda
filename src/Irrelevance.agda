------------------------------------------------------------------------
-- The Agda standard library
--
-- The irrelevance axiom, and some structures for working with irrelevance
------------------------------------------------------------------------

module Irrelevance where

open import Level
open import Data.Product using (Σ) renaming (_,_ to _,′_)
open import Category.Monad

------------------------------------------------------------------------
-- The irrelevance axiom

-- There is no guarantee that this axiom is sound. Use it at your own
-- risk.

postulate
  .irrelevance-axiom : ∀ {a} {A : Set a} → .A → A

{-# BUILTIN IRRAXIOM irrelevance-axiom #-}

------------------------------------------------------------------------
-- "Truncation":  irrelevance as a type

infix 1 Irr_ irr_

record Irr_ {a} (A : Set a) : Set a where
  constructor irr_
  field
    .value : A

.irr-axiom : ∀ {a} {A : Set a} → Irr A → A
irr-axiom (irr v) = irrelevance-axiom v

irr-absorb : ∀ {a} {A : Set a} → .(Irr A) → Irr A
irr-absorb (irr v) = irr v

Irr-monad : ∀ {a} → RawMonad {a} Irr_
Irr-monad = record
  { return = irr_
  ; _>>=_  = bind
  }
  where
    bind : ∀ {A B} → Irr A → (A → Irr B) → Irr B
    bind (irr v) f = irr-absorb (f v)

module _ {a} where
  open RawMonad (Irr-monad {a}) public using () renaming (_>>=_ to _irr>>=_; join to irr-collapse; _>>_ to _irr>>_; _=<<_ to _=<<irr_)

------------------------------------------------------------------------
-- "Existential types": Σ with irrelevant (and implicit) proj₁

infix 4 ⋆,_
infixr 2 ∃_⋆_ ∃-⋆-syntax

record ∃_⋆_ {a b} (A : Set a) (B : .A → Set b) : Set (a ⊔ b) where
  constructor ⋆,_
  field
    .{domain} : A
    value : B domain

∃-⋆-syntax : ∀ {a b} (A : Set a) (B : .A → Set b) → Set (a ⊔ b)
∃-⋆-syntax = ∃_⋆_

syntax ∃-⋆-syntax A (λ v → B) = ∃[ v ∈ A ] B

Σ→∃ : ∀ {a b} {A : Set a} {B : .A → Set b} → Σ A B → ∃ A ⋆ B
Σ→∃ (_ ,′ y) = ⋆, y

------------------------------------------------------------------------
-- "Refinement types": Σ with irrelevant proj₂

infixl 4 _,_
infixl 2 _refineBy_ refineBy-syntax

record _refineBy_ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  constructor _,_
  field
    base : A
    .refinement : B base

refineBy-syntax : ∀ {a b} (A : Set a) (B : A → Set b) → Set (a ⊔ b)
refineBy-syntax = _refineBy_

syntax refineBy-syntax A (λ v → B) = refine v ∈ A by B

Σ→refine : ∀ {a b} {A : Set a} {B : A → Set b} → Σ A B → A refineBy B
Σ→refine (x ,′ y) = x , y

refine-collapse : ∀ {a b₁ b₂} {A : Set a} {B₁ : A → Set b₁} {B₂ : A refineBy B₁ → Set b₂} → A refineBy B₁ refineBy B₂ → A refineBy λ v → Σ (B₁ v) (λ w → B₂ (v , w))
refine-collapse (base , refinement₁ , refinement₂) = base , refinement₁ ,′ refinement₂
