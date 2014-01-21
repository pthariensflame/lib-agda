------------------------------------------------------------------------
-- The Agda standard library
--
-- Strongly typed multisets (bags)
------------------------------------------------------------------------

module Data.Multiset where
open import Level renaming ( zero to zer ; suc to succ )
open import Function
open import Function.Inverse using ( _↔_ )
open import Algebra
open import Algebra.Structures
open import Data.Empty using ( ⊥-elim ; ⊥ )
open import Data.Nat renaming ( _≟_ to _≟′_ ; _⊔_ to _max_ ; _⊓_ to _min_ ; decTotalOrder to ≤-decTotalOrder )
open import Data.Bool using ( Bool ; true ; false )
open import Data.Product using ( _,_ ; _,′_ ; proj₁ ; proj₂ ; _×_ ; Σ ; Σ-syntax ; _-×-_ )
open import Data.Sum using ( inj₁ ; inj₂ ) renaming ( _⊎_ to _⊹_ )
open import Data.List using ( List ; [] ; _∷_ ; [_] ; foldr ; foldl ; reverse )
open import Relation.Nullary
open import Relation.Nullary.Decidable hiding ( map )
open import Relation.Binary
open import Relation.Binary.PropositionalEquality using ( _≡_ ; _≢_ ; refl ; cong ; cong₂ )
open import Data.Nat.Properties using ( ≰⇒> ; ≤×≢⇒< )
open IsDistributiveLattice Data.Nat.Properties.isDistributiveLattice using () renaming ( ∧-cong to max-cong ; ∨-cong to min-cong ; ∧-comm to max-comm ; ∨-comm to min-comm ; ∧-assoc to max-assoc ; ∨-assoc to min-assoc ; absorptive to min-max-absorptive )
open CommutativeSemiringWithoutOne Data.Nat.Properties.⊔-⊓-0-commutativeSemiringWithoutOne using () renaming ( distrib to min-max-distrib ; zero to min-0-zero ; setoid to ℕ-Setoid )
open Setoid ℕ-Setoid using () renaming ( sym to ℕ-sym ; trans to ℕ-trans )
open DecTotalOrder ≤-decTotalOrder using () renaming ( reflexive to ≤-reflexive ; trans to ≤-trans ; antisym to ≤-antisym ; ≤-resp-≈ to ≤-resp-≡ )
open StrictTotalOrder Data.Nat.Properties.strictTotalOrder using () renaming ( irrefl to <-irrefl ; trans to <-trans ; <-resp-≈ to <-resp-≡ ; compare to ℕ-tri )
open CommutativeSemiring Data.Nat.Properties.commutativeSemiring using ( +-cong ; +-comm ; *-cong ; +-assoc )
import Relation.Binary.EqReasoning
open import Relation.Binary.Product.Pointwise using ( _×-setoid_ )

record Multiset {i j} (X : Setoid i j) : Set (i ⊔ j) where
  open Setoid X
  field
    number_hasOf_ : Carrier → ℕ
    respectsEquivalence : {a : Carrier} → {b : Carrier} → a ≈ b → number_hasOf_ a ≡ number_hasOf_ b

open Multiset public using ( number_hasOf_ )

setoid : ∀{i j} → (X : Setoid i j) → Setoid (i ⊔ j) i
setoid X = record {
                Carrier = Multiset X;
                _≈_ = λ v w → (q : Carrier) → number v hasOf q ≡ number w hasOf q;
                isEquivalence =
                    record {
                    refl = λ _ → refl;
                    sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                    trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) } }
  where
    open Setoid X renaming ( refl to ref )

private
  module MultisetSetoid {i j} {X : Setoid i j} = Setoid (setoid {i} {j} X)
open MultisetSetoid public using () renaming ( _≈_ to _≋_ ; refl to ≋-refl ; reflexive to ≋-reflexive ; sym to ≋-sym ; trans to ≋-trans )

_¬≋_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_¬≋_ {X = X} v w = Σ[ q ∈ Carrier ] number v hasOf q ≢ number w hasOf q
  where
    open Setoid X

∅ : ∀{i j} → {X : Setoid i j} → Multiset X
∅ = record { number_hasOf_ = λ _ → 0; respectsEquivalence = λ _ → refl }

_∩_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Multiset X
v ∩ w = record {
          number_hasOf_ = λ a → number v hasOf a max number w hasOf a;
          respectsEquivalence =
            λ {a} {b} a-≈-b →
              max-cong (Multiset.respectsEquivalence v a-≈-b)
              (Multiset.respectsEquivalence w a-≈-b) }

_∪_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Multiset X
v ∪ w = record {
          number_hasOf_ = λ a → number v hasOf a min number w hasOf a;
          respectsEquivalence =
            λ {a} {b} a-≈-b →
              min-cong (Multiset.respectsEquivalence v a-≈-b)
              (Multiset.respectsEquivalence w a-≈-b) }

_⊎_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Multiset X
v ⊎ w = record {
          number_hasOf_ = λ a → number v hasOf a + number w hasOf a;
          respectsEquivalence =
            λ {a} {b} a-≈-b →
              +-cong (Multiset.respectsEquivalence v a-≈-b)
              (Multiset.respectsEquivalence w a-≈-b) }

_∖_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Multiset X
v ∖ w = record {
          number_hasOf_ = λ a → number v hasOf a ∸ number w hasOf a;
          respectsEquivalence =
            λ {a} {b} a-≈-b →
              cong₂ _∸_ (Multiset.respectsEquivalence v a-≈-b)
              (Multiset.respectsEquivalence w a-≈-b) }

_⊠_ : ∀{i j k l} → {X : Setoid i j} → {Y : Setoid k l} → Multiset X → Multiset Y → Multiset (X ×-setoid Y)
v ⊠ w = record {
          number_hasOf_ =
            λ x → number v hasOf proj₁ x * number w hasOf proj₂ x;
          respectsEquivalence =
            λ a≈b →
              *-cong (Multiset.respectsEquivalence v (proj₁ a≈b))
              (Multiset.respectsEquivalence w (proj₂ a≈b)) }

fromList : ∀{i j} → {{X : DecSetoid i j}} → List (DecSetoid.Carrier X) → Multiset (DecSetoid.setoid X)
fromList [] = ∅
fromList {{X}} (x ∷ xs) = record {
                            number_hasOf_ = λ q → numOf q ⌊ q ≟ x ⌋;
                            respectsEquivalence = respEq }
  where
    open DecSetoid X renaming ( refl to ref ; setoid to X-setoid )
    
    oldMS : Multiset X-setoid
    oldMS = fromList xs
    
    numOf : Carrier → Bool → ℕ
    numOf r true = suc (number oldMS hasOf r)
    numOf r false = number oldMS hasOf r

    respEq : {a : Carrier} → {b : Carrier} → a ≈ b → numOf a ⌊ a ≟ x ⌋ ≡ numOf b ⌊ b ≟ x ⌋
    respEq {a} {b} a≈b with a ≟ x | b ≟ x
    ... | yes _ | yes _ = cong suc (Multiset.respectsEquivalence oldMS {a} {b} a≈b)
    ... | no _ | no _ = Multiset.respectsEquivalence oldMS {a} {b} a≈b
    ... | yes a≈x | no b≈x→⊥ = ⊥-elim (b≈x→⊥ (trans (sym a≈b) a≈x))
    ... | no a≈x→⊥ | yes b≈x = ⊥-elim (a≈x→⊥ (trans a≈b b≈x))

singleton : ∀{i j} → {{X : DecSetoid i j}} → DecSetoid.Carrier X → Multiset (DecSetoid.setoid X)
singleton {{X}} x = record { number_hasOf_ = λ q → numOf q ⌊ q ≟ x ⌋; respectsEquivalence = respEq }
  where
    open DecSetoid X renaming ( refl to ref ; setoid to X-setoid )
    
    numOf : Carrier → Bool → ℕ
    numOf r true = 1
    numOf r false = 0

    respEq : {a : Carrier} → {b : Carrier} → a ≈ b → numOf a ⌊ a ≟ x ⌋ ≡ numOf b ⌊ b ≟ x ⌋
    respEq {a} {b} a≈b with a ≟ x | b ≟ x
    ... | yes _ | yes _ = refl
    ... | no _ | no _ = refl
    ... | yes a≈x | no b≈x→⊥ = ⊥-elim (b≈x→⊥ (trans (sym a≈b) a≈x))
    ... | no a≈x→⊥ | yes b≈x = ⊥-elim (a≈x→⊥ (trans a≈b b≈x))

∅-≋-fromList : ∀{i j} → (X : DecSetoid i j) → ∅ ≋ fromList {{X}} []
∅-≋-fromList X _ = refl

singleton-≋-fromList-multiple : ∀{i j} → (X : DecSetoid i j) → (x : DecSetoid.Carrier X) → (xs : List (DecSetoid.Carrier X)) → (singleton {{X}} x ⊎ fromList {{X}} xs) ≋ fromList {{X}} (x ∷ xs)
singleton-≋-fromList-multiple X x xs q with q ≟ x
  where
    open DecSetoid X renaming ( refl to ref ; setoid to X-setoid )
... | yes _ = refl
... | no _ = refl

singleton-≋-fromList-single : ∀{i j} → (X : DecSetoid i j) → (x : DecSetoid.Carrier X) → singleton {{X}} x ≋ fromList {{X}} [ x ]
singleton-≋-fromList-single X x q = ℕ-trans (+-comm 0 (number singleton {{X}} x hasOf q)) (singleton-≋-fromList-multiple X x [] q)

foldr-singleton-≋-fromList : ∀{i j} → (X : DecSetoid i j) → (xs : List (DecSetoid.Carrier X)) → foldr (λ x v → singleton {{X}} x ⊎ v) ∅ xs ≋ fromList {{X}} xs
foldr-singleton-≋-fromList {_} {_} _ [] _ = refl
foldr-singleton-≋-fromList {i} {j} X (x ∷ xs) q with q ≟ x
  where
    open DecSetoid X renaming ( refl to ref ; setoid to X-setoid )
... | yes p = cong suc (foldr-singleton-≋-fromList {i} {j} X xs q)
... | no ¬p = foldr-singleton-≋-fromList {i} {j} X xs q

⊎-monoid : ∀{i j} → Setoid i j → Monoid (i ⊔ j) i
⊎-monoid {i} {j} X = record {
                       Carrier = Multiset X;
                       _≈_ = _≋_;
                       _∙_ = _⊎_;
                       ε = ∅;
                       isMonoid =
                         record {
                         isSemigroup =
                           record {
                           isEquivalence = Setoid.isEquivalence (setoid X);
                           assoc =
                             λ x y z q →
                               +-assoc (number x hasOf q) (number y hasOf q) (number z hasOf q);
                           ∙-cong = λ u≈v x≈y q → +-cong (u≈v q) (x≈y q) };
                         identity =
                           (λ _ _ → refl) , (λ x q → +-comm (number x hasOf q) 0) } }
  where
    open Setoid X renaming ( refl to ref ; sym to symm ; trans to tran )

distributiveLattice : ∀{i j} → (X : Setoid i j) → DistributiveLattice (i ⊔ j) i
distributiveLattice X = record {
                          Carrier = Multiset X;
                          _≈_ = _≋_;
                          _∨_ = _∪_;
                          _∧_ = _∩_;
                          isDistributiveLattice =
                            record {
                            isLattice =
                              record {
                              isEquivalence =
                                record {
                                refl = λ _ → refl;
                                sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                                trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) };
                              ∨-comm = λ x y q → min-comm (number x hasOf q) (number y hasOf q);
                              ∨-assoc =
                                λ x y z q →
                                  min-assoc (number x hasOf q) (number y hasOf q) (number z hasOf q);
                              ∨-cong = λ nu-≡-nx nv-≡-ny q → min-cong (nu-≡-nx q) (nv-≡-ny q);
                              ∧-comm = λ x y q → max-comm (number x hasOf q) (number y hasOf q);
                              ∧-assoc =
                                λ x y z q →
                                  max-assoc (number x hasOf q) (number y hasOf q) (number z hasOf q);
                              ∧-cong = λ nu-≡-nx nv-≡-ny q → max-cong (nu-≡-nx q) (nv-≡-ny q);
                              absorptive =
                                (λ x y q →
                                   proj₁ min-max-absorptive (number x hasOf q) (number y hasOf q))
                                ,
                                (λ x y q →
                                   proj₂ min-max-absorptive (number x hasOf q) (number y hasOf q)) };
                            ∨-∧-distribʳ =
                              λ z x y q →
                                proj₂ min-max-distrib (number z hasOf q) (number x hasOf q)
                                (number y hasOf q) } }
 where
   open Setoid X renaming ( refl to ref )

commutativeSemiringWithoutOne : ∀{i j} → (X : Setoid i j) → CommutativeSemiringWithoutOne (i ⊔ j) i
commutativeSemiringWithoutOne X = record {
                                    Carrier = Multiset X;
                                    _≈_ = _≋_;
                                    _+_ = _∩_;
                                    _*_ = _∪_;
                                    0# = ∅;
                                    isCommutativeSemiringWithoutOne =
                                      record {
                                      isSemiringWithoutOne =
                                        record {
                                        +-isCommutativeMonoid =
                                          record {
                                          isSemigroup =
                                            record {
                                            isEquivalence =
                                              record {
                                              refl = λ _ → refl;
                                              sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                                              trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) };
                                            assoc =
                                              λ x y z q →
                                                max-assoc (number x hasOf q) (number y hasOf q) (number z hasOf q);
                                            ∙-cong = λ g h q → max-cong (g q) (h q) };
                                          identityˡ = λ _ _ → refl;
                                          comm = λ x y q → max-comm (number x hasOf q) (number y hasOf q) };
                                        *-isSemigroup =
                                          record {
                                          isEquivalence =
                                            record {
                                            refl = λ _ → refl;
                                            sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                                            trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) };
                                          assoc =
                                            λ x y z q →
                                              min-assoc (number x hasOf q) (number y hasOf q) (number z hasOf q);
                                          ∙-cong = λ g h q → min-cong (g q) (h q) };
                                        distrib =
                                          (λ x y z q →
                                             proj₁ min-max-distrib (number x hasOf q) (number y hasOf q)
                                             (number z hasOf q))
                                          ,
                                          (λ x y z q →
                                             proj₂ min-max-distrib (number x hasOf q) (number y hasOf q)
                                             (number z hasOf q));
                                        zero =
                                          (λ x q → proj₁ min-0-zero (number x hasOf q)) ,
                                          (λ x q → proj₂ min-0-zero (number x hasOf q)) };
                                      *-comm =
                                        λ x y q → min-comm (number x hasOf q) (number y hasOf q) } }
 where
   open Setoid X renaming ( refl to ref )

_⊆_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊆_ {X = X} v w = (q : Carrier) → number v hasOf q ≤ number w hasOf q
  where
    open Setoid X

_⊇_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊇_ {X = X} v w = (q : Carrier) → number v hasOf q ≥ number w hasOf q
  where
    open Setoid X

_⊂_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊂_ {X = X} v w = ((q : Carrier) → number v hasOf q ≤ number w hasOf q) × (Σ[ q ∈ Carrier ] (number v hasOf q < number w hasOf q))
  where
    open Setoid X

_⊃_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊃_ {X = X} v w = ((q : Carrier) → number v hasOf q ≥ number w hasOf q) × (Σ[ q ∈ Carrier ] (number v hasOf q > number w hasOf q))
  where
    open Setoid X

_⊈_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊈_ {X = X} v w = (q : Carrier) → number v hasOf q > number w hasOf q
  where
    open Setoid X

_⊉_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊉_ {X = X} v w = (q : Carrier) → number v hasOf q < number w hasOf q
  where
    open Setoid X

_⊄_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊄_ {X = X} v w = (Σ[ q ∈ Carrier ] number v hasOf q > number w hasOf q) ⊹ ((q : Carrier) → number v hasOf q ≥ number w hasOf q)
  where
    open Setoid X

_⊅_ : ∀{i j} → {X : Setoid i j} → Multiset X → Multiset X → Set i
_⊅_ {X = X} v w = (Σ[ q ∈ Carrier ] number v hasOf q < number w hasOf q) ⊹ ((q : Carrier) → number v hasOf q ≤ number w hasOf q)
  where
    open Setoid X

⊆×¬≋⇒⊂ : ∀{i j} → {X : Setoid i j} → (_⊆_ {X = X} -×- _¬≋_ {X = X}) ⇒ _⊂_ {X = X}
⊆×¬≋⇒⊂ {X = X} {v} {w} (nv≤nw , q , vq≢wq) = nv≤nw ,′ q , ≤×≢⇒< (nv≤nw q ,′ vq≢wq)

⊆-poset : ∀{i j} → (X : Setoid i j) → Poset (i ⊔ j) i i
⊆-poset X = record {
              Carrier = Multiset X;
              _≈_ = _≋_;
              _≤_ = _⊆_;
              isPartialOrder =
                record {
                isPreorder =
                  record {
                  isEquivalence =
                    record {
                    refl = λ _ → refl;
                    sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                    trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) };
                  reflexive = λ {v} {w} nv≡nw q → ≤-reflexive (nv≡nw q);
                  trans = λ {u} {v} {w} nv≤nw nu≤nv q → ≤-trans (nv≤nw q) (nu≤nv q) };
                antisym = λ {v} {w} nv≤nw nw≤nv q → ≤-antisym (nv≤nw q) (nw≤nv q) } }
  where
    open Setoid X renaming ( refl to ref )

⊇-poset : ∀{i j} → (X : Setoid i j) → Poset (i ⊔ j) i i
⊇-poset X = record {
              Carrier = Multiset X;
              _≈_ = _≋_;
              _≤_ = _⊇_;
              isPartialOrder =
                record {
                isPreorder =
                  record {
                  isEquivalence =
                    record {
                    refl = λ _ → refl;
                    sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                    trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) };
                  reflexive = λ {v} {w} nv≡nw q → ≤-reflexive (ℕ-sym (nv≡nw q));
                  trans = λ {u} {v} {w} nv≤nw nu≤nv q → ≤-trans (nu≤nv q) (nv≤nw q) };
                antisym = λ {v} {w} nv≤nw nw≤nv q → ≤-antisym (nw≤nv q) (nv≤nw q) } }
  where
    open Setoid X renaming ( refl to ref )

⊂-strictPartialOrder : ∀{i j} → (X : Setoid i j) → StrictPartialOrder (i ⊔ j) i i
⊂-strictPartialOrder X = record {
                           Carrier = Multiset X;
                           _≈_ = _≋_;
                           _<_ = _⊂_;
                           isStrictPartialOrder =
                             record {
                             isEquivalence =
                               record {
                               refl = λ _ → refl;
                               sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                               trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) };
                             irrefl =
                               λ {v} {w} nv-≡-nw v⊂w →
                                 <-irrefl (nv-≡-nw (proj₁ (proj₂ v⊂w))) (proj₂ (proj₂ v⊂w));
                             trans =
                               λ {u} {v} {w} u⊂v v⊂w →
                                 (λ q → ≤-trans (proj₁ u⊂v q) (proj₁ v⊂w q)) ,
                                 proj₁ (proj₂ u⊂v) ,
                                 ≤-trans (proj₂ (proj₂ u⊂v)) (proj₁ v⊂w (proj₁ (proj₂ u⊂v)));
                             <-resp-≈ =
                               (λ {u} {v} {w} nv-≡-nw u⊂v →
                                  (λ q → proj₁ ≤-resp-≡ (nv-≡-nw q) (proj₁ u⊂v q)) ,
                                  proj₁ (proj₂ u⊂v) ,
                                  proj₁ <-resp-≡ (nv-≡-nw (proj₁ (proj₂ u⊂v))) (proj₂ (proj₂ u⊂v)))
                               ,
                               (λ {u} {v} {w} nv-≡-nw v⊂u →
                                  (λ q → proj₂ ≤-resp-≡ (nv-≡-nw q) (proj₁ v⊂u q)) ,
                                  proj₁ (proj₂ v⊂u) ,
                                  proj₂ <-resp-≡ (nv-≡-nw (proj₁ (proj₂ v⊂u)))
                                  (proj₂ (proj₂ v⊂u))) } }
  where
    open Setoid X renaming ( refl to ref )

⊃-strictPartialOrder : ∀{i j} → (X : Setoid i j) → StrictPartialOrder (i ⊔ j) i i
⊃-strictPartialOrder X = record {
                           Carrier = Multiset X;
                           _≈_ = _≋_;
                           _<_ = _⊃_;
                           isStrictPartialOrder =
                             record {
                             isEquivalence =
                               record {
                               refl = λ _ → refl;
                               sym = λ na-≡-nb q → ℕ-sym (na-≡-nb q);
                               trans = λ na-≡-nb nb-≡-nc q → ℕ-trans (na-≡-nb q) (nb-≡-nc q) };
                             irrefl =
                               λ {v} {w} nv-≡-nw v⊃w →
                                 <-irrefl (ℕ-sym (nv-≡-nw (proj₁ (proj₂ v⊃w)))) (proj₂ (proj₂ v⊃w));
                             trans =
                               λ {u} {v} {w} u⊃v v⊃w →
                                 (λ q → ≤-trans (proj₁ v⊃w q) (proj₁ u⊃v q)) ,
                                 proj₁ (proj₂ u⊃v) ,
                                 ≤-trans (s≤s (proj₁ v⊃w (proj₁ (proj₂ u⊃v)))) (proj₂ (proj₂ u⊃v));
                             <-resp-≈ =
                               (λ {u} {v} {w} nv-≡-nw u⊃v →
                                  (λ q → proj₂ ≤-resp-≡ (nv-≡-nw q) (proj₁ u⊃v q)) ,
                                  proj₁ (proj₂ u⊃v) ,
                                  proj₂ <-resp-≡ (nv-≡-nw (proj₁ (proj₂ u⊃v))) (proj₂ (proj₂ u⊃v)))
                               ,
                               (λ {u} {v} {w} nv-≡-nw v⊃u →
                                  (λ q → proj₁ ≤-resp-≡ (nv-≡-nw q) (proj₁ v⊃u q)) ,
                                  proj₁ (proj₂ v⊃u) ,
                                  proj₁ <-resp-≡ (nv-≡-nw (proj₁ (proj₂ v⊃u)))
                                  (proj₂ (proj₂ v⊃u))) } }
  where
    open Setoid X renaming ( refl to ref )
