------------------------------------------------------------------------
-- The Agda standard library
--
-- Lenticuloids in residual representation
------------------------------------------------------------------------

module Category.Lens where
open import Level renaming ( zero to ℓzero ; suc to ℓsuc ; lift to ℓlift )
open import Function
open import Relation.Binary
open import Relation.Binary.Indexed as I using ( _at_ )
open import Data.Product
open import Relation.Binary.Product.Pointwise
open import Data.Sum
open import Relation.Binary.Sum
open import Data.Empty
open import Data.Unit
open import Data.Bool hiding ( T )
open import Data.Nat using ( ℕ ; zero ; suc )
open import Data.Fin using ( Fin ; zero ; suc )
open import Data.Vec using ( Vec ; [] ; _∷_ )
open import Relation.Binary.Vec.Pointwise using ( Pointwise ; ext )
open import Function.Inverse hiding ( id ; _∘_ )
open import Function.Equality hiding ( id ; _∘_ ; const ) renaming ( ≡-setoid to Π-≡-setoid )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; refl ; subst ; inspect ; [_] ) renaming ( setoid to ≡-setoid ; cong to ≡-cong ; sym to ≡-sym ; trans to ≡-trans )

private
  constIxSetoid : {aℓ a≈ℓ : Level} → Setoid aℓ a≈ℓ → ∀{iℓ} {I : Set iℓ} → I.Setoid I aℓ a≈ℓ
  constIxSetoid A = record {
                           Carrier = const (Setoid.Carrier A);
                           _≈_ = Setoid._≈_ A;
                           isEquivalence =
                           record {
                           refl = Setoid.refl A;
                           sym = Setoid.sym A;
                           trans = Setoid.trans A } }
  
  ⊥-eq : {x y : ⊥} {wℓ : Level} {W : Set wℓ} → x ≡ y → W
  ⊥-eq {()}

record Isomorphism {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} (Source : I.Setoid Index sℓ s≈ℓ) (Target : I.Setoid Index tℓ t≈ℓ) : Set (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) where
  constructor isomorphism
  field
    transition : {ix : Index} → Inverse (Source at ix) (Target at ix)
  
  invert : Isomorphism Target Source
  invert = record { transition = λ {ix} → sym (transition {ix}) }

identityIsomorphism : {iℓ vℓ v≈ℓ : Level} {Index : Set iℓ} (Value : I.Setoid Index vℓ v≈ℓ) → Isomorphism Value Value
identityIsomorphism {Index = Index} Value = isomorphism
                                              (λ {ix} →
                                                 record {
                                                 to = record { _⟨$⟩_ = id; cong = id };
                                                 from = record { _⟨$⟩_ = id; cong = id };
                                                 inverse-of =
                                                   record {
                                                   left-inverse-of = λ x → V-refl {ix} {x};
                                                   right-inverse-of = λ x → V-refl {ix} {x} } })
  where
    open I.Setoid Value public using () renaming ( refl to V-refl )

Inverse→Isomorphism : {sℓ s≈ℓ tℓ t≈ℓ : Level} {Source : Setoid sℓ s≈ℓ} {Target : Setoid tℓ t≈ℓ} → Inverse Source Target → Isomorphism {Index = ⊤} (constIxSetoid Source) (constIxSetoid Target)
Inverse→Isomorphism inv = isomorphism inv

record Lens {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} (Source : I.Setoid Index sℓ s≈ℓ) (Target : I.Setoid Index tℓ t≈ℓ) : Set (ℓsuc (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)) where
  constructor lens
  field
    {Residue} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    transition : {ix : Index} → Inverse (Source at ix) (Target at ix ×-setoid Residue)

trivialLens : {vℓ v≈ℓ : Level} (Value : Setoid vℓ v≈ℓ) → Lens {Index = ⊤} (constIxSetoid Value) (constIxSetoid (≡-setoid ⊤))
trivialLens {vℓ} {v≈ℓ} Value = lens {Residue = Lift-setoid {vℓ} {v≈ℓ} {v≈ℓ} {vℓ} Value}
                                 (record {
                                  to =
                                    record { _⟨$⟩_ = λ v → tt ,′ ℓlift v; cong = λ p → refl ,′ ℓlift p };
                                  from = record { _⟨$⟩_ = extract; cong = from-cong };
                                  inverse-of =
                                    record { left-inverse-of = λ _ → V-refl; right-inverse-of = right-inverse } })
  where
    open Setoid Value public using () renaming ( Carrier to V ; _≈_ to _V≈_ ; refl to V-refl ; sym to V-sym ; trans to V-trans )
    open Setoid (Lift-setoid {vℓ} {v≈ℓ} {v≈ℓ} {vℓ} Value) public using () renaming ( _≈_ to _ℓV≈_ )
    
    extract : ⊤ × Lift V → V
    extract (tt , ℓlift v) = v
    
    from-cong : {x y : ⊤ × Lift V} → x ⟨ _≡_ ×-Rel _ℓV≈_ ⟩ y → extract x V≈ extract y
    from-cong {tt , ℓlift _} {tt , ℓlift _} (refl , ℓlift p) = p
    
    right-inverse : (x : ⊤ × Lift V) → tt , ℓlift (extract x) ⟨ _≡_ ×-Rel _ℓV≈_ ⟩ x
    right-inverse (tt , ℓlift v) = refl ,′ ℓlift V-refl

vacuousLens : {iℓ vℓ v≈ℓ : Level} {Index : Set iℓ} (Value : I.Setoid Index vℓ v≈ℓ) → Lens (constIxSetoid (≡-setoid ⊥)) Value
vacuousLens {iℓ} {vℓ} {v≈ℓ} {Index} Value = lens {Residue = ≡-setoid (Lift ⊥)}
                                              (λ {ix} →
                                                 record {
                                                 to = record { _⟨$⟩_ = λ {()}; cong = ⊥-eq };
                                                 from =
                                                   record {
                                                   _⟨$⟩_ = λ {(_ , ℓlift ())};
                                                   cong = ⊥-eq ∘′ ≡-cong lower ∘′ proj₂ };
                                                 inverse-of =
                                                   record {
                                                   left-inverse-of = λ {()};
                                                   right-inverse-of = λ {(_ , ℓlift ())} } })
  where
    open I.Setoid Value public using () renaming ( Carrier to V ; _≈_ to _V≈_ ; refl to V-refl ; sym to V-sym ; trans to V-trans )

Isomorphism→Lens : {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} {Source : I.Setoid Index sℓ s≈ℓ} {Target : I.Setoid Index tℓ t≈ℓ} → Isomorphism Source Target → Lens Source Target
Isomorphism→Lens (isomorphism transition) = lens {Residue = ≡-setoid (Lift ⊤)}
                                              (λ {ix} →
                                                 record {
                                                 to =
                                                   record {
                                                   _⟨$⟩_ = λ x → Inverse.to transition ⟨$⟩ x ,′ ℓlift tt;
                                                   cong = λ p → cong (Inverse.to transition) p ,′ refl };
                                                 from =
                                                   record {
                                                   _⟨$⟩_ = λ {(t , ℓlift tt) → Inverse.from transition ⟨$⟩ t};
                                                   cong = λ {(p , refl) → cong (Inverse.from transition) p} };
                                                 inverse-of =
                                                   record {
                                                   left-inverse-of = Inverse.left-inverse-of transition;
                                                   right-inverse-of =
                                                     λ {(t , ℓlift tt)
                                                          → Inverse.right-inverse-of transition t ,′ refl} } })

record Prism {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} (Source : I.Setoid Index sℓ s≈ℓ) (Target : I.Setoid Index tℓ t≈ℓ) : Set (ℓsuc (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)) where
  constructor prism
  field
    {Residue} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    transition : {ix : Index} → Inverse (Source at ix) (Target at ix ⊎-setoid Residue)

vacuousPrism : {vℓ v≈ℓ : Level} (Value : Setoid vℓ v≈ℓ) → Prism {Index = ⊤} (constIxSetoid Value) (constIxSetoid (≡-setoid ⊥))
vacuousPrism {vℓ} {v≈ℓ} Value = prism {Residue = Lift-setoid {vℓ} {v≈ℓ} {v≈ℓ} {vℓ} Value}
                                  (λ {ix} →
                                     record {
                                     to = record { _⟨$⟩_ = λ v → inj₂ (ℓlift v); cong = λ p → ₂∼₂ (ℓlift p) };
                                     from = record { _⟨$⟩_ = extract; cong = from-cong };
                                     inverse-of =
                                       record { left-inverse-of = λ _ → V-refl; right-inverse-of = right-inverse } })
  where
    open Setoid Value public using () renaming ( Carrier to V ; _≈_ to _V≈_ ; refl to V-refl ; sym to V-sym ; trans to V-trans )
    open Setoid (Lift-setoid {vℓ} {v≈ℓ} {v≈ℓ} {vℓ} Value) public using () renaming ( _≈_ to _ℓV≈_ )
    
    extract : ⊥ ⊎ Lift V → V
    extract (inj₁ ())
    extract (inj₂ (ℓlift v)) = v
    
    from-cong : {x y : ⊥ ⊎ Lift V} → x ⟨ _≡_ ⊎-Rel _ℓV≈_ ⟩ y → extract x V≈ extract y
    from-cong (₁∼₂ ())
    from-cong (₁∼₁ p) = ⊥-eq p
    from-cong (₂∼₂ (ℓlift p)) = p
    
    right-inverse : (x : ⊥ ⊎ Lift V) → inj₂ (ℓlift (extract x)) ⟨ _≡_ ⊎-Rel _ℓV≈_ ⟩ x
    right-inverse (inj₁ ())
    right-inverse (inj₂ (ℓlift _)) = ₂∼₂ (ℓlift V-refl)

Isomorphism→Prism : {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} {Source : I.Setoid Index sℓ s≈ℓ} {Target : I.Setoid Index tℓ t≈ℓ} → Isomorphism Source Target → Prism Source Target
Isomorphism→Prism (isomorphism transition) = prism {Residue = ≡-setoid (Lift ⊥)}
                                               (λ {ix} →
                                                  record {
                                                  to =
                                                    record {
                                                    _⟨$⟩_ = λ x → inj₁ (Inverse.to transition ⟨$⟩ x);
                                                    cong = λ p → ₁∼₁ (cong (Inverse.to transition) p) };
                                                  from =
                                                    record {
                                                    _⟨$⟩_ =
                                                      λ {(inj₁ t) → Inverse.from transition ⟨$⟩ t; (inj₂ (ℓlift ()))};
                                                    cong =
                                                      λ { {inj₁ _} {inj₁ _} (₁∼₁ p) → cong (Inverse.from transition) p;
                                                          {inj₂ (ℓlift ())} {inj₁ _} (); {inj₁ _} {inj₂ (ℓlift ())} (₁∼₂ ());
                                                          {inj₂ (ℓlift ())} {inj₂ (ℓlift ())} (₂∼₂ _)} };
                                                  inverse-of =
                                                    record {
                                                    left-inverse-of = Inverse.left-inverse-of transition;
                                                    right-inverse-of =
                                                      λ {(inj₁ t) → ₁∼₁ (Inverse.right-inverse-of transition t);
                                                         (inj₂ (ℓlift ()))} } })

record PLens {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} (Source : I.Setoid Index sℓ s≈ℓ) (Target : I.Setoid Index tℓ t≈ℓ) : Set (ℓsuc (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)) where
  constructor plens
  field
    {Residue} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    {Residue′} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    transition : {ix : Index} → Inverse (Source at ix) ((Target at ix ×-setoid Residue) ⊎-setoid Residue′)

Isomorphism→PLens : {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} {Source : I.Setoid Index sℓ s≈ℓ} {Target : I.Setoid Index tℓ t≈ℓ} → Isomorphism Source Target → PLens Source Target
Isomorphism→PLens {Index = Index} {Source = Source} {Target = Target} (isomorphism transition) = plens {Residue = ≡-setoid (Lift ⊤)} {Residue′ = ≡-setoid (Lift ⊥)}
                                                                                                   (λ {ix} →
                                                                                                      record {
                                                                                                      to =
                                                                                                        record {
                                                                                                        _⟨$⟩_ = λ x → inject (Inverse.to transition ⟨$⟩ x);
                                                                                                        cong = λ p → ₁∼₁ (cong (Inverse.to transition) p , refl) };
                                                                                                      from =
                                                                                                        record {
                                                                                                        _⟨$⟩_ = λ x → Inverse.from transition ⟨$⟩ extract x;
                                                                                                        cong = λ {i} {j} → from-cong i j };
                                                                                                      inverse-of =
                                                                                                        record {
                                                                                                        left-inverse-of = Inverse.left-inverse-of transition;
                                                                                                        right-inverse-of = right-inverse {ix} } })
  where
    open I.Setoid Source public using () renaming ( Carrier to S ; _≈_ to _S≈_ )
    open I.Setoid Target public using () renaming ( Carrier to T ; _≈_ to _T≈_ )
    
    inject : ∀{ix} → T ix → T ix × Lift ⊤ ⊎ Lift ⊥
    inject x = inj₁ (x ,′ ℓlift tt)
    
    extract : ∀{ix} → T ix × Lift ⊤ ⊎ Lift ⊥ → T ix
    extract (inj₁ (t , ℓlift tt)) = t
    extract (inj₂ (ℓlift ()))
    
    from-cong : ∀{ix} → (i j : T ix × Lift ⊤ ⊎ Lift ⊥) → i ⟨ _T≈_ ×-Rel _≡_ ⊎-Rel _≡_ ⟩ j → (Inverse.from transition ⟨$⟩ extract i) S≈ (Inverse.from transition ⟨$⟩ extract j)
    from-cong (inj₁ (_ , ℓlift tt)) (inj₁ (_ , ℓlift tt)) (₁∼₁ (t≈ , refl)) = cong (Inverse.from transition) t≈
    from-cong (inj₁ _) (inj₂ (ℓlift ())) (₁∼₂ ())
    from-cong (inj₂ (ℓlift ())) (inj₁ _) ()
    from-cong (inj₂ (ℓlift ())) (inj₂ (ℓlift ())) (₂∼₂ _)
    
    right-inverse : ∀{ix} → (x : T ix × Lift ⊤ ⊎ Lift ⊥) → inject (Inverse.to transition ⟨$⟩ (Inverse.from transition ⟨$⟩ extract x)) ⟨ _T≈_ ×-Rel _≡_ ⊎-Rel _≡_ ⟩ x
    right-inverse (inj₁ (t , ℓlift tt)) = ₁∼₁ (Inverse.right-inverse-of transition t ,′ refl)
    right-inverse (inj₂ (ℓlift ()))

Lens→PLens : {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} {Source : I.Setoid Index sℓ s≈ℓ} {Target : I.Setoid Index tℓ t≈ℓ} → Lens Source Target → PLens Source Target
Lens→PLens {Index = Index} {Source = Source} {Target = Target} (lens {Residue = Residue} transition) = plens {Residue = Residue} {Residue′ = ≡-setoid (Lift ⊥)}
                                                                           (λ {ix} →
                                                                              record {
                                                                              to =
                                                                                record {
                                                                                _⟨$⟩_ = λ x → inj₁ (Inverse.to transition ⟨$⟩ x);
                                                                                cong = λ x → ₁∼₁ (cong (Inverse.to transition) x) };
                                                                              from =
                                                                                record {
                                                                                _⟨$⟩_ = λ x → Inverse.from transition ⟨$⟩ extract x;
                                                                                cong = λ {i} {j} → from-cong ix i j };
                                                                              inverse-of =
                                                                                record {
                                                                                left-inverse-of = Inverse.left-inverse-of transition;
                                                                                right-inverse-of =
                                                                                  λ {(inj₁ x) → ₁∼₁ (Inverse.right-inverse-of transition x);
                                                                                     (inj₂ (ℓlift ()))} } })
  where
    open I.Setoid Source public using () renaming ( Carrier to S ; _≈_ to _S≈_ )
    open I.Setoid Target public using () renaming ( Carrier to T ; _≈_ to _T≈_ )
    open Setoid Residue using () renaming ( Carrier to R ; _≈_ to _R≈_ )
    
    extract : ∀{ix} → T ix × R ⊎ Lift ⊥ → T ix × R
    extract (inj₁ (t , r)) = t ,′ r
    extract (inj₂ (ℓlift ()))
    
    from-cong : (ix : Index) →
                  (i j : (T ix × R) ⊎ Lift ⊥) →
                  ((_T≈_ ×-Rel _R≈_) ⊎-Rel _≡_) i j →
                  Inverse.from transition ⟨$⟩ extract i S≈
                  Inverse.from transition ⟨$⟩ extract j
    from-cong ix (inj₁ _) (inj₁ _) (₁∼₁ p) = cong (Inverse.from transition) p
    from-cong ix (inj₁ _) (inj₂ (ℓlift ())) (₁∼₂ ())
    from-cong ix (inj₂ (ℓlift ())) (inj₁ _) ()
    from-cong ix (inj₂ (ℓlift ())) (inj₂ (ℓlift ())) (₂∼₂ _)

Prism→PLens : {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} {Source : I.Setoid Index sℓ s≈ℓ} {Target : I.Setoid Index tℓ t≈ℓ} → Prism Source Target → PLens Source Target
Prism→PLens {Index = Index} {Source = Source} {Target = Target} (prism {Residue = Residue} transition) = plens {Residue = ≡-setoid (Lift ⊤)} {Residue′ = Residue}
                                                                                                           (λ {ix} →
                                                                                                              record {
                                                                                                              to =
                                                                                                                record {
                                                                                                                _⟨$⟩_ = λ x → inject (Inverse.to transition ⟨$⟩ x);
                                                                                                                cong = λ {i} {j} → to-cong {ix} i j };
                                                                                                              from =
                                                                                                                record {
                                                                                                                _⟨$⟩_ = λ x → Inverse.from transition ⟨$⟩ extract x;
                                                                                                                cong = λ {i} {j} → from-cong {ix} i j };
                                                                                                              inverse-of =
                                                                                                                record {
                                                                                                                left-inverse-of = left-inverse {ix};
                                                                                                                right-inverse-of = right-inverse {ix} } })
  where
    open I.Setoid Source public using () renaming ( Carrier to S ; _≈_ to _S≈_ )
    open I.Setoid Target public using () renaming ( Carrier to T ; _≈_ to _T≈_ )
    open Setoid Residue using () renaming ( Carrier to R ; _≈_ to _R≈_ )
    
    extract : ∀{ix} → T ix × Lift ⊤ ⊎ R → T ix ⊎ R
    extract (inj₁ (t , ℓlift tt)) = inj₁ t
    extract (inj₂ r) = inj₂ r
    
    inject : ∀{ix} → T ix ⊎ R → T ix × Lift ⊤ ⊎ R
    inject (inj₁ t) = inj₁ (t ,′ ℓlift tt)
    inject (inj₂ r) = inj₂ r
    
    to-cong : ∀{ix} → (i j : S ix) → i S≈ j → inject (Inverse.to transition ⟨$⟩ i) ⟨ _T≈_ ×-Rel _≡_ ⊎-Rel _R≈_ ⟩ inject (Inverse.to transition ⟨$⟩ j)
    to-cong i j p with Inverse.to transition ⟨$⟩ i | Inverse.to transition ⟨$⟩ j | cong (Inverse.to transition) {i} {j} p
    to-cong _ _ _ | inj₁ _ | inj₁ _ | ₁∼₁ t≈ = ₁∼₁ (t≈ ,′ refl)
    to-cong _ _ _ | inj₁ _ | inj₂ _ | ₁∼₂ ()
    to-cong _ _ _ | inj₂ _ | inj₁ _ | ()
    to-cong _ _ _ | inj₂ _ | inj₂ _ | ₂∼₂ r≈ = ₂∼₂ r≈
    
    from-cong : ∀{ix} → (i j : T ix × Lift ⊤ ⊎ R) → i ⟨ _T≈_ ×-Rel _≡_ ⊎-Rel _R≈_ ⟩ j → (Inverse.from transition ⟨$⟩ extract i) S≈ (Inverse.from transition ⟨$⟩ extract j)
    from-cong (inj₁ (_ , ℓlift tt)) (inj₁ (_ , ℓlift tt)) (₁∼₁ (t≈ , refl)) = cong (Inverse.from transition) (₁∼₁ t≈)
    from-cong (inj₁ _) (inj₂ _) (₁∼₂ ())
    from-cong (inj₂ _) (inj₁ _) ()
    from-cong (inj₂ _) (inj₂ _) (₂∼₂ r≈) = cong (Inverse.from transition) (₂∼₂ r≈)
    
    left-inverse : ∀{ix} → (x : S ix) → (Inverse.from (transition {ix}) ⟨$⟩ extract (inject (Inverse.to (transition {ix}) ⟨$⟩ x))) S≈ x
    left-inverse {ix} x with Inverse.to (transition {ix}) ⟨$⟩ x | Inverse.left-inverse-of (transition {ix}) x
    left-inverse _ | inj₁ _ | p = p
    left-inverse _ | inj₂ _ | p = p
    
    right-inverse : ∀{ix} → (x : T ix × Lift ⊤ ⊎ R) → inject (Inverse.to (transition {ix}) ⟨$⟩ (Inverse.from (transition {ix}) ⟨$⟩ extract x)) ⟨ _T≈_ ×-Rel _≡_ ⊎-Rel _R≈_ ⟩ x
    right-inverse {ix} (inj₁ (t , ℓlift tt)) with Inverse.to (transition {ix}) ⟨$⟩ (Inverse.from (transition {ix}) ⟨$⟩ inj₁ t) | Inverse.right-inverse-of (transition {ix}) (inj₁ t)
    right-inverse (inj₁ (_ , ℓlift tt)) | inj₁ _ | ₁∼₁ t≈ = ₁∼₁ (t≈ ,′ refl)
    right-inverse (inj₁ (_ , ℓlift tt)) | inj₂ _ | ()
    right-inverse {ix} (inj₂ r) with Inverse.to (transition {ix}) ⟨$⟩ (Inverse.from (transition {ix}) ⟨$⟩ inj₂ r) | Inverse.right-inverse-of (transition {ix}) (inj₂ r)
    right-inverse (inj₂ _) | inj₁ _ | ₁∼₂ ()
    right-inverse (inj₂ _) | inj₂ _ | ₂∼₂ r≈ = ₂∼₂ r≈

private
  module TraversalDefs {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} (Source : I.Setoid Index sℓ s≈ℓ) (Target : I.Setoid Index tℓ t≈ℓ)
           (Residue : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)) (Residue′ : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ))
           (elems : ℕ) where
    open I.Setoid Source using () renaming ( Carrier to S ; _≈_ to _S≈_ ; refl to S-refl ; reflexive to S-reflexive ; sym to S-sym ; trans to S-trans )
    open I.Setoid Target using () renaming ( Carrier to T ; _≈_ to _T≈_ ; refl to T-refl ; reflexive to T-reflexive ; sym to T-sym ; trans to T-trans )
    open Setoid Residue using () renaming ( Carrier to R ; _≈_ to _R≈_ ; refl to R-refl ; reflexive to R-reflexive ; sym to R-sym ; trans to R-trans )
    open Setoid Residue′ using () renaming ( Carrier to R′ ; _≈_ to _R′≈_ ; refl to R′-refl ; reflexive to R′-reflexive ; sym to R′-sym ; trans to R′-trans )
    
    Carrier : (ix : Index) → Set (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    Carrier ix = Vec (T ix × R) elems ⊎ R′
    
    data _≈_ {ix ix′ : Index} : (x : Carrier ix) (y : Carrier ix′) → Set (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) where
      ₁≈₁ : ∀{x y} → Pointwise (λ {(xt , xr) (yt , yr) → xt T≈ yt × xr R≈ yr}) x y → inj₁ x ≈ inj₁ y
      ₂≈₂ : ∀{x y} → x R′≈ y → inj₂ x ≈ inj₂ y
    
    Res-refl : ∀{ix} (x : Carrier ix) → x ≈ x
    Res-refl (inj₁ x) = ₁≈₁ (ext (λ _ → T-refl , R-refl))
    Res-refl (inj₂ x) = ₂≈₂ R′-refl
    
    Res-sym : ∀{ix ix′} (x : Carrier ix) (y : Carrier ix′) (x≈y : x ≈ y) → y ≈ x
    Res-sym (inj₁ _) (inj₁ _) (₁≈₁ (ext x≈y)) = ₁≈₁
                                                  (ext
                                                   (λ i → let xt≈yt , xr≈yr = x≈y i in T-sym xt≈yt , R-sym xr≈yr))
    Res-sym (inj₁ _) (inj₂ _) ()
    Res-sym (inj₂ _) (inj₁ _) ()
    Res-sym (inj₂ _) (inj₂ _) (₂≈₂ x≈y) = ₂≈₂ (R′-sym x≈y)
    
    Res-trans : ∀{ix ix′ ix″} (x : Carrier ix) (y : Carrier ix′) (z : Carrier ix″) (x≈y : x ≈ y) (y≈z : y ≈ z) → x ≈ z
    Res-trans (inj₁ _) (inj₁ _) (inj₁ _) (₁≈₁ (ext x≈y)) (₁≈₁ (ext y≈z)) = ₁≈₁
                                                                             (ext
                                                                              (λ i →
                                                                                 let xt≈yt , xr≈yr = x≈y i
                                                                                     yt≈zt , yr≈zr = y≈z i
                                                                                 in T-trans xt≈yt yt≈zt , R-trans xr≈yr yr≈zr))
    Res-trans (inj₁ _) (inj₁ _) (inj₂ _) (₁≈₁ (ext _)) ()
    Res-trans (inj₁ _) (inj₂ _) (inj₁ _) () ()
    Res-trans (inj₁ _) (inj₂ _) (inj₂ _) () (₂≈₂ _)
    Res-trans (inj₂ _) (inj₁ _) (inj₁ _) () (₁≈₁ (ext _))
    Res-trans (inj₂ _) (inj₁ _) (inj₂ _) () ()
    Res-trans (inj₂ _) (inj₂ _) (inj₁ _) (₂≈₂ _) ()
    Res-trans (inj₂ _) (inj₂ _) (inj₂ _) (₂≈₂ x≈y) (₂≈₂ y≈z) = ₂≈₂ (R′-trans x≈y y≈z)
    
    Result : I.Setoid Index (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    Result = record {
               Carrier = Carrier;
               _≈_ = _≈_;
               isEquivalence =
                 record {
                 refl = λ {_} {x} → Res-refl x;
                 sym = λ {_} {_} {x} {y} x≈y → Res-sym x y x≈y;
                 trans =
                   λ {_} {_} {_} {x} {y} {z} x≈y y≈z → Res-trans x y z x≈y y≈z } }

record NETraversal {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} (Source : I.Setoid Index sℓ s≈ℓ) (Target : I.Setoid Index tℓ t≈ℓ) : Set (ℓsuc (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)) where
  constructor netraversal
  field
    {Residue} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    {Residue′} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    {elems} : ℕ
  
  module Defs = TraversalDefs Source Target Residue Residue′ elems
  open Defs
  
  field
    transition : {ix : Index} → Inverse (Source at ix) (Target at ix ×-setoid Result at ix)

record Traversal {iℓ sℓ s≈ℓ tℓ t≈ℓ : Level} {Index : Set iℓ} (Source : I.Setoid Index sℓ s≈ℓ) (Target : I.Setoid Index tℓ t≈ℓ) : Set (ℓsuc (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)) where
  constructor traversal
  field
    {Residue} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    {Residue′} : Setoid (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ) (iℓ ⊔ sℓ ⊔ tℓ ⊔ s≈ℓ ⊔ t≈ℓ)
    {elems} : ℕ
  
  module Defs = TraversalDefs Source Target Residue Residue′ elems
  open Defs
  
  field
    transition : {ix : Index} → Inverse (Source at ix) (Result at ix)
