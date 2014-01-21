------------------------------------------------------------------------
-- The Agda standard library
--
-- Thrists with statically-known length
------------------------------------------------------------------------

module Data.Vec.Thrist where
open import Level renaming ( zero to ℓzero ; suc to ℓsuc ; lift to ℓlift )
open import Function
open import Data.Product renaming ( map to Σ-map ; zip to Σ-zip )
open import Data.Unit renaming ( setoid to ⊤-setoid ; decSetoid to ⊤-decSetoid )
open import Data.Empty
open import Data.Nat renaming ( _⊔_ to _max_ ; _⊓_ to _min_ )
open import Data.Fin renaming ( _+_ to _+′_ ; suc to Fin-suc ; pred to Fin-pred )
open import Relation.Binary
open import Relation.Binary.Indexed as Ix using ( _at_ )
open import Algebra
open import Relation.Binary.PropositionalEquality renaming ( [_] to ⟦_⟧ ; setoid to ≡-setoid )
open import Relation.Binary.HeterogeneousEquality using ( _≅_ ; ≅-to-≡ ; ≡-to-≅ ) renaming ( refl to refl′ ; sym to sym′ ; trans to trans′ ; subst to subst′ ; cong to cong′ )
open import Data.Nat.Properties using ( n+0≡n ) renaming ( commutativeSemiring to ℕ-commutativeSemiring )
open CommutativeSemiring ℕ-commutativeSemiring using ( +-comm ; +-identity ; *-comm )
import Relation.Binary.Indexed.EqReasoning as IxEqR

infixr 5 _∷_ _++_
data Thrist {i j} {I : Set i} (C : I → I → Set j) : ℕ → I → I → Set (i ⊔ j) where
  [] : {x : I} → Thrist {i} {j} {I} C zero x x
  _∷_ : {x : I} → {y : I} → C x y → {n : ℕ} → {z : I} → Thrist {i} {j} {I} C n y z → Thrist {i} {j} {I} C (suc n) x z

_++_ : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {m : ℕ} → {x : I} → {y : I} → {z : I} → Thrist {i} {j} {I} C n x y → Thrist {i} {j} {I} C m y z → Thrist {i} {j} {I} C (n + m) x z
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

[_] : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {x : I} → {y : I} → C x y → Thrist {i} {j} {I} C 1 x y
[ x ] = x ∷ []

join : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {m : ℕ} → {x : I} → {y : I} → Thrist {i} {i ⊔ j} {I} (Thrist {i} {j} {I} C m) n x y → Thrist {i} {j} {I} C (n * m) x y
join [] = []
join (cs ∷ css) = cs ++ join css

infixr 4 _>>=_
_>>=_ : ∀ {i i′ j j′} → {I : Set i} → {C : I → I → Set j} → {I′ : Set i′} → {D : I′ → I′ → Set j′} → {n : ℕ} → {m : ℕ} → {x : I} → {y : I} → Thrist {i} {j} {I} C n x y → {tr : I → I′} → ({x′ : I} → {y′ : I} → C x′ y′ → Thrist {i′} {j′} {I′} D m (tr x′) (tr y′)) → Thrist {i′} {j′} {I′} D (n * m) (tr x) (tr y)
_>>=_ {n = zero} [] f = []
_>>=_ {n = suc n} (c ∷ cs) f = f c ++ (cs >>= f)

map : ∀{i i′ j j′} → {I : Set i} → {C : I → I → Set j} → {I′ : Set i′} → {D : I′ → I′ → Set j′} → {tr : I → I′} → ({x′ : I} → {y′ : I} → C x′ y′ → D (tr x′) (tr y′)) → {n : ℕ} → {x : I} → {y : I} → Thrist {i} {j} {I} C n x y → Thrist {i′} {j′} {I′} D n (tr x) (tr y)
map f [] = []
map f (c ∷ cs) = f c ∷ map f cs

zip : ∀{i i′ i′′ j j′ j′′} → {I : Set i} → {C : I → I → Set j} → {I′ : Set i′} → {D : I′ → I′ → Set j′} → {I′′ : Set i′′} → {E : I′′ → I′′ → Set j′′} → {tr : I → I′ → I′′} → ({x₁′ : I} → {y₁′ : I} → C x₁′ y₁′ → {x₂′ : I′} → {y₂′ : I′} → D x₂′ y₂′ → E (tr x₁′ x₂′) (tr y₁′ y₂′)) → {n : ℕ} → {x₁ : I} → {y₁ : I} → {x₂ : I′} → {y₂ : I′} → Thrist {i} {j} {I} C n x₁ y₁ → Thrist {i′} {j′} {I′} D n x₂ y₂ → Thrist {i′′} {j′′} {I′′} E n (tr x₁ x₂) (tr y₁ y₂)
zip f [] [] = []
zip f (c₁ ∷ cs₁) (c₂ ∷ cs₂) = f c₁ c₂ ∷ zip f cs₁ cs₂

_++[_] : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {x : I} → {y : I} → Thrist C n x y → {z : I} → C y z → Thrist C (suc n) x z
_++[_] {C = C} {n = n} {x = x} cs {z = z} c = subst (λ ¿ → Thrist C ¿ x z) (+-comm n 1) $ cs ++ [ c ]

reverse : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {x : I} → {y : I} → Thrist {i} {j} {I} C n x y → Thrist {i} {j} {I} (flip C) n y x
reverse {i} {j} {I} {C} {zero} {x} {.x} [] = []
reverse {i} {j} {I} {C} {suc n} {x} {y} (c ∷ cs) = reverse cs ++[ c ]

foldr : ∀{i i′ j j′} → {I : Set i} → {C : I → I → Set j} → {I′ : Set i′} → {tr : I → I′} → {A : ℕ → I′ → I′ → Set j′} → ({x′ : I} → {y′ : I} → C x′ y′ → {n′ : ℕ} → {z‵′ : I′} → A n′ (tr y′) z‵′ → A (suc n′) (tr x′) z‵′) → {m : ℕ} → {y : I} → {z‵ : I′} → A m (tr y) z‵ → {n : ℕ} → {x : I} → Thrist C n x y → A (n + m) (tr x) z‵
foldr _ b [] = b
foldr {tr = tr} {A = A} f {m = m} {y = y} {z‵ = z‵} b {n = suc n} {x = x} (_∷_ {x = .x} {y = y₀} c {n = .n} {z = .y} cs) = f c
                                                                                                                             (foldr {tr = tr} {A = A}
                                                                                                                              (λ {x′} {y′} c′ {n′} {z‵′} b′ → f {x′} {y′} c′ {n′} {z‵′} b′) b cs)

foldr‵ : ∀{i j k} → {I : Set i} → {C : I → I → Set j} → {A : ℕ → Set k} → ({x′ : I} → {y′ : I} → C x′ y′ → {n′ : ℕ} → A n′ → A (suc n′)) → {m : ℕ} → A m → {n : ℕ} → {x : I} → {y : I} → Thrist C n x y → A (n + m)
foldr‵ {A = A} f b cs = foldr {A = λ {n tt tt → A n}} (λ {c′ {z‵′ = tt} b′ → f c′ b′}) b cs

foldr′ : ∀{i i′ j j′} → {I : Set i} → {C : I → I → Set j} → {I′ : Set i′} → {tr : I → I′} → {A : I′ → I′ → Set j′} → ({x′ : I} → {y′ : I} → C x′ y′ → {z‵′ : I′} → A (tr y′) z‵′ → A (tr x′) z‵′) → {m : ℕ} → {y : I} → {z‵ : I′} → A (tr y) z‵ → {n : ℕ} → {x : I} → Thrist C n x y → A (tr x) z‵
foldr′ {A = A} f b cs = foldr {A = λ _ x′ y′ → A x′ y′} (λ c′ b′ → f c′ b′) {m = 0} b cs

foldr‵′ : ∀{i j k} → {I : Set i} → {C : I → I → Set j} → {A : Set k} → ({x′ : I} → {y′ : I} → C x′ y′ → A → A) → A → {n : ℕ} → {x : I} → {y : I} → Thrist C n x y → A
foldr‵′ {A = A} f b cs = foldr {A = λ {_ tt tt → A}} (λ {c′ {z‵′ = tt} b′ → f c′ b′}) {m = 0} b cs

foldl : ∀{i i′ j j′} → {I : Set i} → {C : I → I → Set j} → {I′ : Set i′} → {tr : I → I′} → {A : ℕ → I′ → I′ → Set j′} → ({n′ : ℕ} → {x‵′ : I′} → {y′ : I} → A n′ x‵′ (tr y′) → {z′ : I} → C y′ z′ → A (suc n′) x‵′ (tr z′)) → {m : ℕ} → {x‵ : I′} → {y : I} → A m x‵ (tr y) → {n : ℕ} → {z : I} → Thrist C n y z → A (n + m) x‵ (tr z)
foldl _ b [] = b
foldl {tr = tr} {A = A} f {m = m} {x‵ = x‵} b {n = suc n} {z = z} (c ∷ cs) = subst (λ ¿ → A ¿ x‵ (tr z))
                                                                               (trans (+-comm n (suc m)) (cong suc (+-comm m n)))
                                                                               $ foldl {tr = tr} {A = A} f (f {n′ = m} b c) cs

private
  ixMap : ∀{i j k l} → {I : Set i} → {J : Set j} → (J → I) → Ix.Setoid I k l → Ix.Setoid J k l
  ixMap f A-setoid = record {
                        Carrier = A ∘′ f;
                        _≈_ = _≈_;
                        isEquivalence =
                          record { refl = A-refl; sym = A-sym; trans = A-trans } }
    where
      open Ix.Setoid A-setoid renaming ( Carrier to A ; refl to A-refl ; reflexive to A-reflexive ; sym to A-sym ; trans to A-trans )

module Props {i j k} {I : Set i} (C-setoid : Ix.Setoid (I × I) j k) where
  open Ix.Setoid C-setoid renaming ( Carrier to C-× ; refl to ≈-refl ; sym to ≈-sym ; trans to ≈-trans )
  
  private
    C : I → I → Set j
    C = curry′ C-×
    
    _≋_ : {n : ℕ} → {m : ℕ} → {x : I} → {y : I} → {z : I} → {t : I} → Thrist C n x y → Thrist C m z t → Set k
    [] ≋ [] = Lift ⊤
    [] ≋ (_ ∷ _) = Lift ⊥
    (_ ∷ _) ≋ [] = Lift ⊥
    (a ∷ as) ≋ (b ∷ bs) = a ≈ b × as ≋ bs
    
    ≋-refl : {n : ℕ} → {x : I} → {y : I} → (as : Thrist C n x y) → as ≋ as
    ≋-refl [] = ℓlift tt
    ≋-refl (a ∷ as) = ≈-refl ,′ ≋-refl as
    
    ≋-sym : {n : ℕ} → {x : I} → {y : I} → (as : Thrist C n x y) → {m : ℕ} → {z : I} → {t : I} → (bs : Thrist C m z t) → as ≋ bs → bs ≋ as
    ≋-sym [] [] (ℓlift tt) = ℓlift tt
    ≋-sym [] (_ ∷ _) (ℓlift ())
    ≋-sym (_ ∷ _) [] (ℓlift ())
    ≋-sym (a ∷ as) (b ∷ bs) (a≈b , as≋bs) = (≈-sym a≈b) ,′ (≋-sym as bs as≋bs)
    
    ≋-trans : {n : ℕ} → {x : I} → {y : I} → (as : Thrist C n x y) → {m : ℕ} → {z : I} → {t : I} → (bs : Thrist C m z t) → {p : ℕ} → {u : I} → {v : I} → (cs : Thrist C p u v) → as ≋ bs → bs ≋ cs → as ≋ cs
    ≋-trans [] [] [] (ℓlift tt) (ℓlift tt) = ℓlift tt
    ≋-trans [] [] (_ ∷ _) _ (ℓlift ())
    ≋-trans [] (_ ∷ _) [] (ℓlift ()) _
    ≋-trans [] (_ ∷ _) (_ ∷ _) (ℓlift ()) _
    ≋-trans (_ ∷ _) [] [] (ℓlift ()) _
    ≋-trans (_ ∷ _) [] (_ ∷ _) (ℓlift ()) _
    ≋-trans (_ ∷ _) (_ ∷ _) [] _ (ℓlift ())
    ≋-trans (a ∷ as) (b ∷ bs) (c ∷ cs) (a≈b , as≋bs) (b≈c , bs≋cs) = (≈-trans a≈b b≈c) ,′ (≋-trans as bs cs as≋bs bs≋cs)
  
  setoid : Ix.Setoid (ℕ × I × I) (i ⊔ j) k
  setoid = record {
             Carrier = λ {(n , x , y) → Thrist C n x y};
             _≈_ = _≋_;
             isEquivalence =
               record {
               refl = λ {_} {a} → ≋-refl a;
               sym = λ {_} {_} {as} {bs} as≋bs → ≋-sym as bs as≋bs;
               trans =
                 λ {_} {_} {_} {as} {bs} {cs} as≋bs bs≋cs →
                   ≋-trans as bs cs as≋bs bs≋cs } }
  open Ix.Setoid setoid using () renaming ( reflexive to ≋-reflexive )
  
  open IxEqR setoid renaming ( _≈⟨_⟩_ to _≋⟨_⟩_ )
  
  ℕ-≡-trans : {n : ℕ} →
                {x : I} →
                {y : I} →
                (as : Thrist C n x y) →
                {n′ : ℕ} → (ev : n ≡ n′) → as ≅ subst (λ ¿ → Thrist C ¿ x y) ev as
  ℕ-≡-trans {zero} {x} {.x} [] {zero} refl = refl′
  ℕ-≡-trans {suc n} {_} {_} (_ ∷ _) {suc .n} refl = refl′
  
  ∷-cong : {n : ℕ} →
             {x : I} →
             {y : I} →
             (a : C x y) →
             {z : I} →
             (as : Thrist C n y z) →
             {n′ : ℕ} →
             {x′ : I} →
             {y′ : I} →
             (b : C x′ y′) →
             {z′ : I} →
             (bs : Thrist C n′ y′ z′) → a ≈ b → as ≋ bs → (a ∷ as) ≋ (b ∷ bs)
  ∷-cong _ _ _ _ a≈b as≋bs = a≈b , as≋bs

  lift-[_] : {x : I} → {y : I} → {a : C x y} → {x′ : I} → {y′ : I} → {b : C x′ y′} → a ≈ b → [ a ] ≋ [ b ]
  lift-[ a≈b ] = a≈b , ℓlift tt

  ++-[]-identityˡ : {n : ℕ} → {x : I} → {y : I} → (as : Thrist C n x y) → ([] ++ as) ≋ as
  ++-[]-identityˡ as = ≋-refl as

  ++-[]-identityʳ : {n : ℕ} → {x : I} → {y : I} → (as : Thrist C n x y) → (as ++ []) ≋ as
  ++-[]-identityʳ [] = ℓlift tt
  ++-[]-identityʳ (a ∷ as) = ≈-refl ,′ ++-[]-identityʳ as

  ++-[]-identity : {n : ℕ} → {x : I} → {y : I} → (as : Thrist C n x y) → (([] ++ as) ≋ as) × ((as ++ []) ≋ as)
  ++-[]-identity as = ++-[]-identityˡ as ,′ ++-[]-identityʳ as
  
  ++-cong : {n₁ : ℕ} →
              {x₁ : I} →
              {y₁ : I} →
              {as₁ : Thrist C n₁ x₁ y₁} →
              {m₁ : ℕ} →
              {z₁ : I} →
              {bs₁ : Thrist C m₁ y₁ z₁} →
              {n₂ : ℕ} →
              {x₂ : I} →
              {y₂ : I} →
              {as₂ : Thrist C n₂ x₂ y₂} →
              {m₂ : ℕ} →
              {z₂ : I} →
              {bs₂ : Thrist C m₂ y₂ z₂} →
              as₁ ≋ as₂ → bs₁ ≋ bs₂ → (as₁ ++ bs₁) ≋ (as₂ ++ bs₂)
  ++-cong {zero} {._} {._} {[]} {zero} {_} {[]} {zero} {._} {._} {[]} {zero} {_} {[]} (ℓlift tt) (ℓlift tt) = ℓlift tt
  ++-cong {zero} {._} {._} {[]} {zero} {_} {[]} {zero} {._} {_} {[]} {suc _} {_} {b₂ ∷ bs₂} (ℓlift tt) (ℓlift ())
  ++-cong {zero} {._} {._} {[]} {zero} {_} {[]} {suc _} {_} {._} {a₂ ∷ as₂} {zero} {_} {[]} (ℓlift ()) (ℓlift tt)
  ++-cong {zero} {._} {._} {[]} {zero} {_} {[]} {suc _} {_} {_} {a₂ ∷ as₂} {suc _} {_} {b₂ ∷ bs₂} (ℓlift ()) (ℓlift ())
  ++-cong {zero} {._} {_} {[]} {suc _} {_} {b₁ ∷ bs₁} {zero} {._} {._} {[]} {zero} {_} {[]} (ℓlift tt) (ℓlift ())
  ++-cong {zero} {._} {_} {[]} {suc _} {_} {b₁ ∷ bs₁} {zero} {._} {_} {[]} {suc _} {_} {b₂ ∷ bs₂} (ℓlift tt) b₁∷bs₁≋b₂∷bs₂ = b₁∷bs₁≋b₂∷bs₂
  ++-cong {zero} {._} {_} {[]} {suc _} {_} {b₁ ∷ bs₁} {suc _} {_} {._} {a₂ ∷ as₂} {zero} {_} {[]} (ℓlift ()) (ℓlift ())
  ++-cong {zero} {._} {_} {[]} {suc _} {_} {b₁ ∷ bs₁} {suc _} {_} {_} {a₂ ∷ as₂} {suc _} {_} {b₂ ∷ bs₂} (ℓlift ()) _
  ++-cong {suc _} {_} {._} {a₁ ∷ as₁} {zero} {_} {[]} {zero} {._} {._} {[]} {zero} {_} {[]} (ℓlift ()) (ℓlift tt)
  ++-cong {suc _} {_} {._} {a₁ ∷ as₁} {zero} {_} {[]} {zero} {._} {_} {[]} {suc _} {_} {b₂ ∷ bs₂} (ℓlift ()) (ℓlift ())
  ++-cong {suc _} {_} {._} {a₁ ∷ as₁} {zero} {_} {[]} {suc _} {_} {._} {a₂ ∷ as₂} {zero} {z₂} {[]} (a₁≈a₂ , as₁≋as₂) (ℓlift tt) = a₁≈a₂ ,
                                                                                                                                      ++-cong {_} {_} {_} {as₁} {_} {_} {[]} {_} {_} {_} {as₂} {_} {_}
                                                                                                                                      {[]} as₁≋as₂ (≋-refl {zero} {z₂} {_} [])
  ++-cong {suc _} {_} {._} {a₁ ∷ as₁} {zero} {_} {[]} {suc _} {_} {_} {a₂ ∷ as₂} {suc _} {_} {b₂ ∷ bs₂} _ (ℓlift ())
  ++-cong {suc _} {_} {_} {a₁ ∷ as₁} {suc _} {_} {b₁ ∷ bs₁} {zero} {._} {._} {[]} {zero} {_} {[]} (ℓlift ()) (ℓlift ())
  ++-cong {suc _} {_} {_} {a₁ ∷ as₁} {suc _} {_} {b₁ ∷ bs₁} {zero} {._} {_} {[]} {suc _} {_} {b₂ ∷ bs₂} (ℓlift ()) _
  ++-cong {suc _} {_} {_} {a₁ ∷ as₁} {suc _} {_} {b₁ ∷ bs₁} {suc _} {_} {._} {a₂ ∷ as₂} {zero} {_} {[]} _ (ℓlift ())
  ++-cong {suc _} {_} {_} {a₁ ∷ as₁} {suc _} {_} {b₁ ∷ bs₁} {suc _} {_} {_} {a₂ ∷ as₂} {suc _} {_} {b₂ ∷ bs₂} (a₁≈a₂ , as₁≋as₂) b₁∷bs₁≋b₂∷bs₂ = a₁≈a₂ ,
                                                                                                                                                  ++-cong {as₁ = as₁} {bs₁ = b₁ ∷ bs₁} {as₂ = as₂} {bs₂ = b₂ ∷ bs₂}
                                                                                                                                                  as₁≋as₂ b₁∷bs₁≋b₂∷bs₂
  
  ∷-++[⌣]-assoc : {x : I} →
                      {y : I} →
                      (c : C x y) →
                      {n : ℕ} →
                      {z : I} →
                      (cs : Thrist C n y z) →
                      {t : I} → (c′ : C z t) → ((c ∷ cs) ++[ c′ ]) ≋ (c ∷ cs ++[ c′ ])
  ∷-++[⌣]-assoc c [] c′ = ≋-refl (c ∷ c′ ∷ [])
  ∷-++[⌣]-assoc {x} {y} c {suc n} {z} (c′′ ∷ cs) {t} c′ = begin
                                                            (c ∷ c′′ ∷ cs) ++[ c′ ] ≅⟨⟩
                                                            subst (λ ¿ → Thrist C ¿ x t)
                                                            (trans (cong suc (trans (cong suc (+-comm n 1)) refl)) refl)
                                                            (c ∷ c′′ ∷ cs ++ c′ ∷ [])
                                                            ≋⟨ ≋-reflexive {suc (suc (suc n)) , x , t} {suc (suc (n + 1)) , x , t} {subst (λ ¿ → Thrist C ¿ x t)
                                                                                                                                      (trans (cong suc (trans (cong suc (+-comm n 1)) refl)) refl)
                                                                                                                                      (c ∷ c′′ ∷ cs ++ c′ ∷ [])} {c ∷ c′′ ∷ cs ++ c′ ∷ []} (cong (λ n₀ → n₀ ,′ x ,′ t) (sym (trans (cong suc (trans (cong suc (+-comm n 1)) refl)) refl))) (sym′ (ℕ-≡-trans (c ∷ c′′ ∷ cs ++ c′ ∷ []) (trans (cong suc (trans (cong suc (+-comm n 1)) refl)) refl))) ⟩
                                                            c ∷ c′′ ∷ cs ++ c′ ∷ [] ≋⟨ ∷-cong c (c′′ ∷ cs ++ c′ ∷ []) c (subst (λ ¿ → Thrist C ¿ y t) (trans (cong suc (+-comm n 1)) refl)
                                                                                                                           (c′′ ∷ cs ++ c′ ∷ [])) ≈-refl (≋-reflexive (cong (λ n₀ → n₀ , y , t) (trans (cong suc (+-comm n 1)) refl)) (ℕ-≡-trans (c′′ ∷ cs ++ c′ ∷ []) (trans (cong suc (+-comm n 1)) refl))) ⟩
                                                            c ∷
                                                            subst (λ ¿ → Thrist C ¿ y t) (trans (cong suc (+-comm n 1)) refl)
                                                            (c′′ ∷ cs ++ c′ ∷ [])
                                                            ≅⟨⟩ c ∷ (c′′ ∷ cs) ++[ c′ ] ∎
  
  ++[⌣]-cong : {n : ℕ} →
                 {x : I} →
                 {y : I} →
                 {as : Thrist C n x y} →
                 {z : I} →
                 {a : C y z} →
                 {n′ : ℕ} →
                 {x′ : I} →
                 {y′ : I} →
                 {bs : Thrist C n′ x′ y′} →
                 {z′ : I} →
                 {b : C y′ z′} → as ≋ bs → a ≈ b → (as ++[ a ]) ≋ (bs ++[ b ])
  ++[⌣]-cong {zero} {x} {.x} {[]} {_} {_} {zero} {x′} {.x′} {[]} {_} {_} (ℓlift tt) a≈b = lift-[ a≈b ]
  ++[⌣]-cong {zero} {x} {.x} {[]} {_} {_} {suc _} {_} {_} {_ ∷ _} {_} {_} (ℓlift ()) _
  ++[⌣]-cong {suc n} {_} {_} {_ ∷ _} {_} {_} {zero} {x′} {.x′} {[]} {_} {_} (ℓlift ()) _
  ++[⌣]-cong {suc n} {x} {y} {_∷_ {y = y₀} a′ as} {z} {a} {suc n′} {x′} {y′} {_∷_ {y = y₀′} b′ bs} {z′} {b} (a′≈b′ , as≋bs) a≈b = begin
                                                                                                                                    (a′ ∷ as) ++[ a ] ≅⟨⟩
                                                                                                                                    subst (λ ¿ → Thrist C ¿ x z) (trans (cong suc (+-comm n 1)) refl)
                                                                                                                                    (a′ ∷ as ++ a ∷ [])
                                                                                                                                    ≋⟨ ≋-sym (a′ ∷ as ++ a ∷ []) (subst (λ ¿ → Thrist C ¿ x z) (trans (cong suc (+-comm n 1)) refl)
                                                                                                                                                (a′ ∷ as ++ a ∷ [])) (≋-reflexive (cong (λ n₀ → n₀ , x , z) (trans (cong suc (+-comm n 1)) refl)) (ℕ-≡-trans (a′ ∷ as ++ a ∷ []) (trans (cong suc (+-comm n 1)) refl)))
                                                                                                                                    ⟩
                                                                                                                                    a′ ∷ as ++ a ∷ [] ≋⟨ ∷-cong a′ (as ++ a ∷ []) a′ (as ++[ a ]) ≈-refl (≋-reflexive (cong (λ n₀ → n₀ , y₀ , z) (+-comm n 1)) (ℕ-≡-trans (as ++ a ∷ []) (+-comm n 1)))
                                                                                                                                    ⟩
                                                                                                                                    a′ ∷ as ++[ a ] ≋⟨
                                                                                                                                    ∷-cong a′ (as ++[ a ]) b′ (bs ++[ b ]) a′≈b′
                                                                                                                                    (++[⌣]-cong {n} {y₀} {y} {as} {z} {a} {n′} {y₀′} {y′} {bs} {z′} {b}
                                                                                                                                     as≋bs a≈b)
                                                                                                                                    ⟩
                                                                                                                                    b′ ∷ bs ++[ b ] ≋⟨ ∷-cong b′ (bs ++[ b ]) b′ (bs ++ b ∷ []) ≈-refl (≋-sym (bs ++ b ∷ []) (bs ++[ b ]) (≋-reflexive (cong (λ n₀ → n₀ , y₀′ , z′) (+-comm n′ 1)) (ℕ-≡-trans (bs ++ b ∷ []) (+-comm n′ 1))))
                                                                                                                                    ⟩
                                                                                                                                    b′ ∷ bs ++ b ∷ [] ≋⟨ ≋-reflexive (cong (λ n₀ → n₀ , x′ , z′) (trans (cong suc (+-comm n′ 1)) refl)) (ℕ-≡-trans (b′ ∷ bs ++ b ∷ []) (trans (cong suc (+-comm n′ 1)) refl))
                                                                                                                                    ⟩
                                                                                                                                    subst (λ ¿ → Thrist C ¿ x′ z′)
                                                                                                                                    (trans (cong suc (+-comm n′ 1)) refl) (b′ ∷ bs ++ b ∷ [])
                                                                                                                                    ≅⟨⟩ (b′ ∷ bs) ++[ b ] ∎
  
  ++-assoc : {n : ℕ} →
               {x : I} →
               {y : I} →
               (as : Thrist C n x y) →
               {m : ℕ} →
               {z : I} →
               (bs : Thrist C m y z) →
               {p : ℕ} →
               {t : I} →
               (cs : Thrist C p z t) → ((as ++ bs) ++ cs) ≋ (as ++ (bs ++ cs))
  ++-assoc [] [] [] = ℓlift tt
  ++-assoc [] [] (c ∷ cs) = ≋-refl (c ∷ cs)
  ++-assoc [] (b ∷ bs) [] = ≋-refl ((b ∷ bs) ++ [])
  ++-assoc [] (b ∷ bs) (c ∷ cs) = ≋-refl ((b ∷ bs) ++ (c ∷ cs))
  ++-assoc (a ∷ as) [] [] = ++-[]-identityʳ ((a ∷ as) ++ [])
  ++-assoc (a ∷ as) [] (c ∷ cs) = ++-cong {_} {_} {_} {(a ∷ as) ++ []} {_} {_} {c ∷ cs} {_} {_} {_}
                                    {a ∷ as} {_} {_} {c ∷ cs}
                                    (((a ∷ as) ++ []) ≋ (a ∷ as) ∋
                                     ++-[]-identityʳ {_} {_} {_} (a ∷ as))
                                    (≋-refl {_} {_} {_} (c ∷ cs))
  ++-assoc (a ∷ as) (b ∷ bs) [] = ≈-refl ,′ ++-assoc as (b ∷ bs) []
  ++-assoc (a ∷ as) (b ∷ bs) (c ∷ cs) = ≈-refl ,′ ++-assoc as (b ∷ bs) (c ∷ cs)
  
  headTail : {n : ℕ} → {x : I} → {z : I} → (cs : Thrist C (suc n) x z) → Σ[ y ∈ I ] Σ[ c′ ∈ C x y ] Σ[ cs′ ∈ Thrist C n y z ] (cs ≋ (c′ ∷ cs′))
  headTail (_∷_ {y = y} c cs) = y , c , cs , ≋-refl (c ∷ cs)
  
  initLast : {n : ℕ} → {x : I} → {z : I} → (cs : Thrist C (suc n) x z) → Σ[ y ∈ I ] Σ[ cs′ ∈ Thrist C n x y ] Σ[ c′ ∈ C y z ] (cs ≋ (cs′ ++[ c′ ]))
  initLast (c ∷ []) = , ([] , c , ≋-refl [ c ])
  initLast {n = suc n} (_∷_ {x = x′} {y = y′} c {z = z′} cs) with initLast cs
  ... | y , cs′ , c′ , ev = y ,
                              c ∷ cs′ ,
                              c′ ,
                              ≋-trans (c ∷ cs) (c ∷ cs′ ++[ c′ ]) ((c ∷ cs′) ++[ c′ ])
                              (∷-cong c cs c (cs′ ++[ c′ ]) ≈-refl ev)
                              (begin
                               c ∷ cs′ ++[ c′ ] ≋⟨ ∷-cong c (cs′ ++[ c′ ]) c (cs′ ++ c′ ∷ []) ≈-refl (≋-sym (cs′ ++ c′ ∷ []) (cs′ ++[ c′ ]) (≋-reflexive (cong (λ n₀ → n₀ , y′ , z′) (+-comm n 1)) (ℕ-≡-trans (cs′ ++ c′ ∷ []) (+-comm n 1))))
                               ⟩
                               c ∷ cs′ ++ c′ ∷ [] ≅⟨⟩
                               (c ∷ cs′) ++ c′ ∷ [] ≋⟨ ≋-reflexive (cong (λ n₀ → n₀ , x′ , z′) (trans (cong suc (+-comm n 1)) refl)) (ℕ-≡-trans ((c ∷ cs′) ++ c′ ∷ []) (trans (cong suc (+-comm n 1)) refl))
                               ⟩ (c ∷ cs′) ++[ c′ ] ∎)
  
  foldr-∷-cancel : {n : ℕ} → {x : I} → {y : I} → (cs : Thrist C n x y) → foldr {A = Thrist C} _∷_ [] cs ≋ cs
  foldr-∷-cancel {zero} [] = ℓlift tt
  foldr-∷-cancel {suc n} (x₁ ∷ cs) = ≈-refl ,′ foldr-∷-cancel cs
  
  {-foldl-++[⌣]-cancel : {n : ℕ} → {x : I} → {y : I} → (cs : Thrist C n x y) → foldl {A = Thrist C} _++[_] [] cs ≋ cs
  foldl-++[⌣]-cancel xs = ?-}

open Props public

private
  C-setoid : ∀{i j} → {I : Set i} → (I → I → Set j) → Ix.Setoid (I × I) j i
  C-setoid C = record {
                 Carrier = uncurry′ C;
                 _≈_ = λ { {x , y} {x′ , y′} c c′ → x ≡ x′ × y ≡ y′ × c ≅ c′};
                 isEquivalence =
                   record {
                   refl = λ {i} {x} → refl , refl , refl′;
                   sym = λ {(x≡x′ , y≡y′ , c≅c′) → sym x≡x′ , sym y≡y′ , sym′ c≅c′};
                   trans =
                     λ {(x≡x′ , y≡y′ , c≅c′) (x′≡x′′ , y′≡y′′ , c′≅c′′)
                          → trans x≡x′ x′≡x′′ , trans y≡y′ y′≡y′′ , trans′ c≅c′ c′≅c′′} } }

head : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {x : I} → {z : I} → Thrist C (suc n) x z → Σ[ y ∈ I ] C x y
head {I = I} {C = C} {n = n} {x = x} {z = z} cs = proj₁ v , proj₁ (proj₂ v)
  where
    v : Σ[ y ∈ I ] Σ[ c′ ∈ C x y ] Σ[ cs′ ∈ Thrist C n y z ] _
    v = headTail (C-setoid C) cs

tail : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {x : I} → {z : I} → Thrist C (suc n) x z → Σ[ y ∈ I ] Thrist C n y z
tail {I = I} {C = C} {n = n} {x = x} {z = z} cs = proj₁ v , proj₁ (proj₂ (proj₂ v))
  where
    v : Σ[ y ∈ I ] Σ[ c′ ∈ C x y ] Σ[ cs′ ∈ Thrist C n y z ] _
    v = headTail (C-setoid C) cs

init : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {x : I} → {z : I} → Thrist C (suc n) x z → Σ[ y ∈ I ] Thrist C n x y
init {I = I} {C = C} {n = n} {x = x} {z = z} cs = proj₁ v , proj₁ (proj₂ v)
  where
    v : Σ[ y ∈ I ] Σ[ cs′ ∈ Thrist C n x y ] Σ[ c′ ∈ C y z ] _
    v = initLast (C-setoid C) cs

last : ∀{i j} → {I : Set i} → {C : I → I → Set j} → {n : ℕ} → {x : I} → {z : I} → Thrist C (suc n) x z → Σ[ y ∈ I ] C y z
last {I = I} {C = C} {n = n} {x = x} {z = z} cs = proj₁ v , proj₁ (proj₂ (proj₂ v))
  where
    v : Σ[ y ∈ I ] Σ[ cs′ ∈ Thrist C n x y ] Σ[ c′ ∈ C y z ] _
    v = initLast (C-setoid C) cs
