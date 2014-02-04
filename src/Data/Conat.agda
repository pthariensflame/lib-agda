------------------------------------------------------------------------
-- The Agda standard library
--
-- Coinductive "natural" numbers
------------------------------------------------------------------------

module Data.Conat where

open import Coinduction
open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary

------------------------------------------------------------------------
-- The type

data Coℕ : Set where
  zero : Coℕ
  suc  : (n : ∞ Coℕ) → Coℕ

------------------------------------------------------------------------
-- Some operations

suc′ : (n : Coℕ) → Coℕ
suc′ n = suc (♯ n)

fromℕ : ℕ → Coℕ
fromℕ zero    = zero
fromℕ (suc n) = suc′ (fromℕ n)

∞ℕ : Coℕ
∞ℕ = suc (♯ ∞ℕ)

infixl 6 _+_

_+_ : Coℕ → Coℕ → Coℕ
zero  + n = n
suc m + n = suc (♯ (♭ m + n))

------------------------------------------------------------------------
-- Equality

data _≈_ : Coℕ → Coℕ → Set where
  zero :                                zero  ≈ zero
  suc  : ∀ {m n} (m≈n : ∞ (♭ m ≈ ♭ n)) → suc m ≈ suc n

setoid : Setoid _ _
setoid = record
  { Carrier       = Coℕ
  ; _≈_           = _≈_
  ; isEquivalence = record
    { refl  = refl
    ; sym   = sym
    ; trans = trans
    }
  }
  where
  refl : Reflexive _≈_
  refl {zero}  = zero
  refl {suc n} = suc (♯ refl)

  sym : Symmetric _≈_
  sym zero      = zero
  sym (suc m≈n) = suc (♯ sym (♭ m≈n))

  trans : Transitive _≈_
  trans zero      zero      = zero
  trans (suc m≈n) (suc n≈k) = suc (♯ trans (♭ m≈n) (♭ n≈k))

------------------------------------------------------------------------
-- Order

data _≤_ : Coℕ → Coℕ → Set where
  z≤n : ∀ {  n}                      → zero  ≤     n
  s≤s : ∀ {m n} (m≤n : ∞ (♭ m ≤ ♭ n)) → suc m ≤ suc n

poset : Poset _ _ _
poset = record
  { Carrier = Coℕ
  ; _≈_ = _≈_
  ; _≤_ = _≤_
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Setoid.isEquivalence setoid
      ; reflexive = reflexive
      ; trans = trans
      }
    ; antisym = antisym
    }
  }
  where
  reflexive : _≈_ ⇒ _≤_
  reflexive zero = z≤n
  reflexive (suc m≈n) = s≤s (♯ (reflexive (♭ m≈n)))

  trans : Transitive _≤_
  trans z≤n _ = z≤n
  trans (s≤s m≤n) (s≤s n≤p) = s≤s (♯ (trans (♭ m≤n) (♭ n≤p)))

  antisym : Antisymmetric _≈_ _≤_
  antisym z≤n z≤n = zero
  antisym (s≤s m≤n) (s≤s n≤m) = suc (♯ (antisym (♭ m≤n) (♭ n≤m)))

------------------------------------------------------------------------
-- More operations

pred : (n : Coℕ) ⦃ p : fromℕ 1 ≤ n ⦄ → ∞ Coℕ
pred zero ⦃()⦄
pred (suc n) ⦃ s≤s _ ⦄ = n

------------------------------------------------------------------------
-- Other properties

mutual
  data even : Coℕ → Set where
    zero : even zero
    suc : {n : ∞ Coℕ} → ∞ (odd (♭ n)) → even (suc n)
  
  data odd : Coℕ → Set where
    suc : {n : ∞ Coℕ} → ∞ (even (♭ n)) → odd (suc n)

mutual
  even∞ : even ∞ℕ
  even∞ = suc (♯ odd∞)
  
  odd∞ : odd ∞ℕ
  odd∞ = suc (♯ even∞)

even-id→even-suc² : {n : Coℕ} → even n → even (suc′ (suc′ n))
even-id→even-suc² p = suc (♯ suc (♯ p))

odd-id→odd-suc² : {n : Coℕ} → odd n → odd (suc′ (suc′ n))
odd-id→odd-suc² p = suc (♯ suc (♯ p))

twice : Coℕ → Coℕ
twice zero = zero
twice (suc n) = suc (♯ (suc (♯ twice (♭ n))))

twice-even : (n : Coℕ) → even (twice n)
twice-even zero = zero
twice-even (suc n) = suc (♯ suc (♯ twice-even (♭ n)))

suc-twice-odd : (n : Coℕ) → odd (suc′ (twice n))
suc-twice-odd n = suc (♯ twice-even n)

pred-twice-odd : (n : Coℕ) ⦃ p : fromℕ 1 ≤ twice n ⦄ → ∞ (odd (♭ (pred (twice n) ⦃ p ⦄)))
pred-twice-odd zero {{()}}
pred-twice-odd (suc n) {{s≤s m≤n}} = ♯ suc (♯ twice-even (♭ n))
