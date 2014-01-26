------------------------------------------------------------------------
-- The Agda standard library
--
-- Lists with a built-in element uniqueness system (ordered subsets of a setoid)
------------------------------------------------------------------------

module Data.List.Unique where
open import Level renaming ( zero to ℓzero ; suc to ℓsuc ; lift to ℓlift )
open import Function
open import Function.Equality hiding ( _∘_ ) renaming ( setoid to Π-setoid ; ≡-setoid to Π-≡-setoid ; _⇨_ to _⟶-setoid_ ; _⇨′_ to _⟶-≡-setoid_ )
open import Function.Inverse using ( _↔_ ; module Inverse )
open import Data.Empty
open import Data.Nat renaming ( _≟_ to _≟-ℕ_ ; _⊔_ to _max_ ; _⊓_ to _min_ )
open import Data.Fin
open import Relation.Binary
open import Relation.Binary.Indexed as Ix using () renaming ( _=[_]⇒_ to _=⟦_⟧⇒_ )
open import Relation.Binary.PropositionalEquality renaming ( setoid to ≡-setoid ; cong to ≡-cong )
open import Relation.Nullary
open import Relation.Nullary.Decidable renaming ( map to Dec-map )

mutual
  data UList {eℓ e≈ℓ} (Elem : Setoid eℓ e≈ℓ) : Set (eℓ ⊔ e≈ℓ) where
    [] : UList Elem
    _∷_uniq_ : (x : Setoid.Carrier Elem) (xs : UList Elem) (u : x ∉ xs) → UList Elem
  
  data All {eℓ e≈ℓ rℓ} {Elem : Setoid eℓ e≈ℓ} (P : Setoid.Carrier Elem → Set rℓ) : (xs : UList Elem) → Set (eℓ ⊔ e≈ℓ ⊔ rℓ) where
    [] : All P []
    _∷_uniq_ : ∀{x xs} (p : P x) (ps : All P xs) u → All P (x ∷ xs uniq u)
  
  data _∉_ {eℓ e≈ℓ} {Elem : Setoid eℓ e≈ℓ} (x : Setoid.Carrier Elem) : (xs : UList Elem) → Set (eℓ ⊔ e≈ℓ) where
    [] : x ∉ []
    _∷_uniq_ : ∀{x′ xs} (p : x ∉ xs) (ps : All (¬_ ∘′ Setoid._≈_ Elem x) xs) u → x ∉ (x′ ∷ xs uniq u)

data Any {eℓ e≈ℓ rℓ} {Elem : Setoid eℓ e≈ℓ} (P : Setoid.Carrier Elem → Set rℓ) : (xs : UList Elem) → Set (eℓ ⊔ e≈ℓ ⊔ rℓ) where
  hereIn_∷_uniq_ : ∀{x} (p : P x) xs u → Any P (x ∷ xs uniq u)
  thereIn_∷_uniq_ : ∀ x {xs} (ps : Any P xs) u → Any P (x ∷ xs uniq u)

data _∈_ {eℓ e≈ℓ} {Elem : Setoid eℓ e≈ℓ} : (x : Setoid.Carrier Elem) (xs : UList Elem) → Set (eℓ ⊔ e≈ℓ) where
  hereIn_∷_uniq_ : ∀ x xs u → x ∈ (x ∷ xs uniq u)
  thereIn_∷_uniq_ : ∀{x} x′ {xs} (i : x ∈ xs) u → x ∈ (x′ ∷ xs uniq u)

length : ∀{eℓ e≈ℓ} {Elem : Setoid eℓ e≈ℓ} (xs : UList Elem) → ℕ
length [] = 0
length (_ ∷ xs uniq _) = suc (length xs)
  
data _≋_ {eℓ e≈ℓ} {Elem : Setoid eℓ e≈ℓ} : (xs ys : UList Elem) → Set (eℓ ⊔ e≈ℓ) where
  [] : [] ≋ []
  _∷_uniq_,_ : ∀{x y} (p : x ⟨ Setoid._≈_ Elem ⟩ y) {xs ys} (ps : xs ≋ ys) x-uniq y-uniq → (x ∷ xs uniq x-uniq) ≋ (y ∷ ys uniq y-uniq)

UList-setoid : ∀{eℓ e≈ℓ} (Elem : Setoid eℓ e≈ℓ) → Setoid (eℓ ⊔ e≈ℓ) (eℓ ⊔ e≈ℓ)
UList-setoid Elem = record {
                      Carrier = UList Elem;
                      _≈_ = _≋_;
                      isEquivalence =
                        record {
                        refl = λ {xs} → ≋-refl xs;
                        sym = λ {xs} {ys} → ≋-sym xs ys;
                        trans = λ {xs} {ys} {zs} → ≋-trans xs ys zs } }
  where
    open Setoid Elem using () renaming ( refl to E-refl ; sym to E-sym ; trans to E-trans )
    
    ≋-refl : ∀ xs → xs ≋ xs
    ≋-refl [] = []
    ≋-refl (_ ∷ xs uniq u) = E-refl ∷ ≋-refl xs uniq u , u
    
    ≋-sym : ∀ xs ys (ps : xs ≋ ys) → ys ≋ xs
    ≋-sym [] [] [] = []
    ≋-sym [] (_ ∷ _ uniq _) ()
    ≋-sym (_ ∷ _ uniq _) [] ()
    ≋-sym (_ ∷ xs uniq u-x) (_ ∷ ys uniq u-y) (p ∷ ps uniq .u-x , .u-y) = E-sym p ∷ ≋-sym xs ys ps uniq u-y , u-x
    
    ≋-trans : ∀ xs ys zs (psₗ : xs ≋ ys) (psᵣ : ys ≋ zs) → xs ≋ zs
    ≋-trans [] [] [] [] [] = []
    ≋-trans [] [] (_ ∷ _ uniq _) [] ()
    ≋-trans [] (_ ∷ _ uniq _) [] () _
    ≋-trans [] (_ ∷ _ uniq _) (_ ∷ _ uniq _) () _
    ≋-trans (_ ∷ _ uniq _) [] [] () _
    ≋-trans (_ ∷ _ uniq _) [] (_ ∷ _ uniq _) () _
    ≋-trans (_ ∷ _ uniq uₗ) (_ ∷ _ uniq uᵣ) [] (_ ∷ _ uniq .uₗ , .uᵣ) ()
    ≋-trans (_ ∷ xs uniq u-x) (_ ∷ ys uniq u-y) (_ ∷ zs uniq u-z) (pₗ ∷ psₗ uniq .u-x , .u-y) (pᵣ ∷ psᵣ uniq .u-y , .u-z) = E-trans pₗ pᵣ ∷ ≋-trans xs ys zs psₗ psᵣ uniq u-x , u-z

UList-decSetoid : ∀{eℓ e≈ℓ} (Elem : DecSetoid eℓ e≈ℓ) → DecSetoid (eℓ ⊔ e≈ℓ) (eℓ ⊔ e≈ℓ)
UList-decSetoid Elem = record {
                         Carrier = UList E-setoid;
                         _≈_ = _≋_;
                         isDecEquivalence =
                           record {
                           isEquivalence = Setoid.isEquivalence (UList-setoid E-setoid);
                           _≟_ = _≋?_ } }
  where
    open DecSetoid Elem using () renaming ( _≟_ to _E≟_ ; setoid to E-setoid )
    
    _≋?_ : ∀ xs ys → Dec (xs ≋ ys)
    [] ≋? [] = yes []
    [] ≋? (y ∷ ys uniq u) = no proof
      where
        proof : ¬ [] ≋ (y ∷ ys uniq u)
        proof ()
    (x ∷ xs uniq u) ≋? [] = no proof
      where
        proof : ¬ (x ∷ xs uniq u) ≋ []
        proof ()
    (x ∷ xs uniq u-x) ≋? (y ∷ ys uniq u-y) with x E≟ y | xs ≋? ys
    (x ∷ xs uniq u-x) ≋? (y ∷ ys uniq u-y) | yes p | yes ps = yes (p ∷ ps uniq u-x , u-y)
    (x ∷ xs uniq u-x) ≋? (y ∷ ys uniq u-y) | yes _ | no ¬ps = no proof
      where
        proof : ¬ (x ∷ xs uniq u-x) ≋ (y ∷ ys uniq u-y)
        proof (_ ∷ ps uniq .u-x , .u-y) = ¬ps ps
    (x ∷ xs uniq u-x) ≋? (y ∷ ys uniq u-y) | no ¬p | _ = no proof
      where
        proof : ¬ (x ∷ xs uniq u-x) ≋ (y ∷ ys uniq u-y)
        proof (p ∷ _ uniq .u-x , .u-y) = ¬p p

record Π! {aℓ a≈ℓ bℓ b≈ℓ} (From : Setoid aℓ a≈ℓ) (To : Ix.Setoid (Setoid.Carrier From) bℓ b≈ℓ) : Set (aℓ ⊔ a≈ℓ ⊔ bℓ ⊔ b≈ℓ) where
  infixl 5 _⟨$!⟩_
  field
    _⟨$!⟩_ : (x : Setoid.Carrier From) → Ix.Setoid.Carrier To x
    cong! : Setoid._≈_ From =⟦ _⟨$!⟩_ ⟧⇒ Ix.Setoid._≈_ To
    ¬cong! : (¬- Setoid._≈_ From) =⟦ _⟨$!⟩_ ⟧⇒ (¬- Ix.Setoid._≈_ To)
  as-Π : Π From To
  as-Π = record { cong = cong! }
open Π! public hiding ( as-Π )

_⟶!_ : ∀{aℓ a≈ℓ bℓ b≈ℓ} (From : Setoid aℓ a≈ℓ) (To : Setoid bℓ b≈ℓ) → Set (aℓ ⊔ a≈ℓ ⊔ bℓ ⊔ b≈ℓ)
From ⟶! To = Π! From (Setoid.indexedSetoid To)

mutual
  map : ∀{aℓ a≈ℓ bℓ b≈ℓ} {From : Setoid aℓ a≈ℓ} {To : Setoid bℓ b≈ℓ} (f : From ⟶! To) (xs : UList From) → UList To
  map f [] = []
  map f (x ∷ xs uniq x-uniq) = (f ⟨$!⟩ x) ∷ map f xs uniq map-uniq f x xs x-uniq
  
  map-uniq : ∀{aℓ a≈ℓ bℓ b≈ℓ} {From : Setoid aℓ a≈ℓ} {To : Setoid bℓ b≈ℓ}
               (f : From ⟶! To) (x : Setoid.Carrier From) (xs : UList From)
               (x-uniq : x ∉ xs) →
               (f ⟨$!⟩ x) ∉ map f xs
  map-uniq f x [] [] = []
  map-uniq f x (x′ ∷ xs uniq x′-uniq) (p ∷ ps uniq .x′-uniq) = map-uniq f x xs p ∷ map-all-uniq f x xs p ps uniq map-uniq f x′ xs x′-uniq
    
  private
    map-all-uniq : ∀{aℓ a≈ℓ bℓ b≈ℓ} {From : Setoid aℓ a≈ℓ} {To : Setoid bℓ b≈ℓ}
                     (f : From ⟶! To) (x : Setoid.Carrier From) (xs : UList From)
                     (x-uniq : x ∉ xs)
                     (ps : All (λ x′ → ¬ (x ⟨ Setoid._≈_ From ⟩ x′)) xs) →
                     All (λ x′ → ¬ (f ⟨$!⟩ x ⟨ Setoid._≈_ To ⟩ x′)) (map f xs)
    map-all-uniq f x [] [] [] = []
    map-all-uniq f x (x′ ∷ xs uniq x′-uniq) (pₗ ∷ _ uniq .x′-uniq) (pᵣ ∷ psᵣ uniq .x′-uniq) = ¬cong! f pᵣ ∷ map-all-uniq f x xs pₗ psᵣ uniq map-uniq f x′ xs x′-uniq
