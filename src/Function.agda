------------------------------------------------------------------------
-- The Agda standard library
--
-- Simple combinators working solely on and with functions
------------------------------------------------------------------------

module Function where

open import Level

infixr 9 _∘_ _∘′_
infixl 8 _ˢ_ _ˢ′_
infixl 1 _on_ _on′_
infixl 1 _⟨_⟩_ _⟨′_‵⟩_
infixr 0 _-[_]-_ _-[′_‵]-_ _$_ _$′_
infixl 0 _∋_ ∋-syntax

------------------------------------------------------------------------
-- Types

-- Unary functions on a given set.

Fun₁ : ∀ {i} → Set i → Set i
Fun₁ A = A → A

-- Binary functions on a given set.

Fun₂ : ∀ {i} → Set i → Set i
Fun₂ A = A → A → A

------------------------------------------------------------------------
-- Functions

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
      (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
      ((x : A) → C (g x))
f ∘ g = λ x → f (g x)

_∘′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (B → C) → (A → B) → (A → C)
f ∘′ g = _∘_ f g

id : ∀ {a} {A : Set a} → A → A
id x = x

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x = λ _ → x

-- The S combinator. (Written infix as in Conor McBride's paper
-- "Outrageous but Meaningful Coincidences: Dependent type-safe syntax
-- and evaluation".)

_ˢ_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
      ((x : A) (y : B x) → C x y) →
      (g : (x : A) → B x) →
      ((x : A) → C x (g x))
f ˢ g = λ x → f x (g x)

_ˢ′_ : ∀ {a b c}
        {A : Set a} {B : Set b} {C : Set c} →
      (A → B → C) →
      (A → B) →
      (A → C)
_ˢ′_ = _ˢ_

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

flip′ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (A → B → C) → (B → A → C)
flip′ = flip

-- Note that _$_ is right associative, like in Haskell. If you want a
-- left associative infix application operator, use
-- Category.Functor._<$>_, available from
-- Category.Monad.Identity.IdentityMonad.

_$_ : ∀ {a b} {A : Set a} {B : A → Set b} →
      ((x : A) → B x) → ((x : A) → B x)
f $ x = f x

_$′_ : ∀ {a b} {A : Set a} {B : Set b} →
      (A → B) → (A → B)
_$′_ = _$_

_⟨_⟩_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : (x : A) → B x → Set c} →
        (x : A) → ((x′ : A) → (y′ : B x′) → C x′ y′) → (y : B x) → C x y
x ⟨ f ⟩ y = f x y

_⟨′_‵⟩_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
        A → (A → B → C) → B → C
_⟨′_‵⟩_ = _⟨_⟩_

_on_ : ∀ {a b c} {A : Set a} {B : Set b} {C : B → B → Set c} →
       ((x : B) → (y : B) → C x y) → (f : A → B) → ((x : A) → (y : A) → C (f x) (f y))
_*_ on f = λ x y → f x * f y

_on′_ : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
       (B → B → C) → (A → B) → (A → A → C)
_on′_ = _on_

_-[_]-_ : ∀ {a b c d e} {A : Set a} {B : A → Set b} {C : Set c}
            {D : Set d} {E : C → D → Set e} →
          (f : (x : A) → B x → C) → ((x : C) → (y : D) → E x y) → (g : (x : A) → B x → D) → ((x : A) (y : B x) → E (f x y) (g x y))
f -[ _*_ ]- g = λ x y → f x y * g x y

_-[′_‵]-_ : ∀ {a b c d e} {A : Set a} {B : Set b} {C : Set c}
            {D : Set d} {E : Set e} →
          (A → B → C) → (C → D → E) → (A → B → D) → (A → B → E)
_-[′_‵]-_ = _-[_]-_

-- In basic Agda you cannot annotate every subexpression with a type
-- signature. This function (and its associated syntax) can be used instead.

_∋_ : ∀ {a} (A : Set a) → A → A
A ∋ x = x

∋-syntax : ∀ {a} (A : Set a) → A → A
∋-syntax = _∋_

syntax ∋-syntax A x = x ∻ A

-- Case expressions (to be used with pattern-matching lambdas, see
-- README.Case).

infix 0 case_return_of_ case_of_

case_return_of_ :
  ∀ {a b} {A : Set a}
  (x : A) (B : A → Set b) → ((x : A) → B x) → B x
case x return B of f = f x

case_of_ : ∀ {a b} {A : Set a} {B : Set b} → A → (A → B) → B
case x of f = case x return _ of f
