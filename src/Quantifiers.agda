------------------------------------------------------------------------
-- The Agda standard library
--
-- Additional quantifiers
------------------------------------------------------------------------

module Quantifiers where
open import Level renaming ( zero to zer ; suc to succ )
open import Function
open import Data.Product
open import Data.Empty
open import Data.Bool hiding ( _≟_ )
open import Data.Nat renaming ( _⊔_ to _max_ ; _⊓_ to _min_ ; decTotalOrder to ℕ-decTotalOrder )
open import Data.Nat.Properties using ( n≤1+n ; 1+n≰n ; ≤×≢⇒< )
open import Data.Vec
open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming ( [_] to ⟦_⟧ )
open import Relation.Nullary
open import Relation.Nullary.Decidable
open DecTotalOrder ℕ-decTotalOrder using () renaming ( reflexive to ≤-reflexive ; trans to ≤-trans )

data All {i j} {A : Set i} (P : A → Set j) : {n : ℕ} → (xs : Vec A n) → Set (i ⊔ j) where
  [] : All {i} {j} {A} P {zero} []
  _∷_ : {n : ℕ} → {x : A} → {xs : Vec A n} → P x → All {i} {j} {A} P {n} xs → All {i} {j} {A} P {suc n} (x ∷ xs)

map-All : ∀{i j k} → {A : Set i} → {P : A → Set j} → {Q : A → Set k} → ({x : A} → P x → Q x) → {n : ℕ} → {xs : Vec A n} → All {i} {j} {A} P {n} xs → All {i} {k} {A} Q {n} xs
map-All f [] = []
map-All f (ev ∷ evs) = f ev ∷ map-All f evs

data _∈_by_ {i j} {A : Set i} : A → {n : ℕ} → Vec A n → (A → A → Set j) → Set (i ⊔ succ j) where
  here  : {n : ℕ} → {x : A} → {y : A} → {xs : Vec A n} → {_≈_ : A → A → Set j} → (x≈y : x ≈ y) → x ∈ y ∷ xs by _≈_
  there : {n : ℕ} → {x : A} → {y : A} → {xs : Vec A n} → {_≈_ : A → A → Set j} → (x∈xs : x ∈ xs by _≈_) → x ∈ y ∷ xs by _≈_

-- there exists finitely many
∃⁺ : ∀{i j k} → {A : Set i} → (A → A → Set k) → (A → Set j) → Set (i ⊔ j ⊔ succ k)
∃⁺ {A = A} _≈_ P = Σ[ n ∈ ℕ ] Σ[ xs ∈ Vec A n ] (All P xs × ((x : A) → P x → x ∈ xs by _≈_))

-- for all but finitely many
∀⁺ : ∀{i j k} → {A : Set i} → (A → A → Set k) → (A → Set j) → Set (i ⊔ j ⊔ succ k)
∀⁺ {A = A} _≈_ P = Σ[ n ∈ ℕ ] Σ[ xs ∈ Vec A n ] All (λ (x : A) → ¬ P x) xs × ((x : A) → ¬ P x → x ∈ xs by _≈_)

open Data.Product public using ( ∃! )

{- checks for proper behavior -}
--------------------------------

private
  ℕ-ub→fin : (n : ℕ) → ∃⁺ _≡_ (_≥_ n)
  ℕ-ub→fin zero = suc zero , [ zero ] , z≤n ∷ [] , (λ {zero z≤n → here refl})
  ℕ-ub→fin (suc n) = suc (proj₁ (ℕ-ub→fin n)) ,
                       suc n ∷ proj₁ (proj₂ (ℕ-ub→fin n)) ,
                       ≤-reflexive refl ∷
                       map-All (λ x≤n → ≤-trans x≤n (n≤1+n n))
                       (proj₁ (proj₂ (proj₂ (ℕ-ub→fin n))))
                       , uniq-proof
    where
      uniq-proof : (x : ℕ) → x ≤ suc n → x ∈ suc n ∷ proj₁ (proj₂ (ℕ-ub→fin n)) by _≡_
      uniq-proof zero z≤n = there (proj₂ (proj₂ (proj₂ (ℕ-ub→fin n))) zero z≤n)
      uniq-proof (suc x) (s≤s x≤n) with suc x ≟ suc n
      ... | yes 1+x≡1+n = here 1+x≡1+n
      ... | no 1+x≢1+n = there
                           (proj₂ (proj₂ (proj₂ (ℕ-ub→fin n))) (suc x)
                            (≤×≢⇒< (x≤n , (λ x≡n → 1+x≢1+n (cong suc x≡n)))))
  
  ℕ-lb→cofin′ : (n : ℕ) → ∀⁺ _≡_ (_<_ n)
  ℕ-lb→cofin′ zero = suc zero ,
                      [ zero ] ,
                      (λ ()) ∷ [] ,
                      (λ {zero _ → here refl; (suc x) 1≰0 → ⊥-elim (1≰0 (s≤s z≤n))})
  ℕ-lb→cofin′ (suc n) = suc (proj₁ (ℕ-lb→cofin′ n)) ,
                         suc n ∷ proj₁ (proj₂ (ℕ-lb→cofin′ n)) ,
                         1+n≰n ∷
                         map-All (λ {x} 1+n≰x 2+n≤x → 1+n≰x (≤-trans (n≤1+n (suc n)) 2+n≤x))
                         (proj₁ (proj₂ (proj₂ (ℕ-lb→cofin′ n))))
                         , uniq-proof
    where
      uniq-proof : (x : ℕ) → suc (suc n) ≰ x → x ∈ suc n ∷ proj₁ (proj₂ (ℕ-lb→cofin′ n)) by _≡_
      uniq-proof zero _ = there (proj₂ (proj₂ (proj₂ (ℕ-lb→cofin′ n))) zero (λ ()))
      uniq-proof (suc x) 2+n≰x with suc x ≟ suc n
      ... | yes 1+x≡1+n = here 1+x≡1+n
      ... | no 1+x≢1+n = there
                           (proj₂ (proj₂ (proj₂ (ℕ-lb→cofin′ n))) (suc x)
                            (λ {(s≤s n≤x)
                                  → 2+n≰x
                                    (s≤s (≤×≢⇒< (n≤x , (λ n≡x → 1+x≢1+n (cong suc (sym n≡x))))))}))
  
  ℕ-lb→cofin : (n : ℕ) → ∀⁺ _≡_ (_≤_ n)
  ℕ-lb→cofin zero = zero , [] , [] , (λ x 0≰x → ⊥-elim {succ zer} {x ∈ [] by _≡_} (0≰x z≤n))
  ℕ-lb→cofin (suc n) = ℕ-lb→cofin′ n
  
  +-uniq : (m : ℕ) → (n : ℕ) → ∃! _≡_ (λ (r : ℕ) → m + n ≡ r)
  +-uniq m n = m + n , refl {zer} {ℕ} {m + n} , id {zer}
