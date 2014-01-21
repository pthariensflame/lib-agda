------------------------------------------------------------------------
-- The Agda standard library
--
-- Dependent function inverses
------------------------------------------------------------------------

module Function.Inverse.Dependent where
open import Level
open import Relation.Binary
open import Relation.Binary.Indexed as Ix using ( _at_ ; _on_ )
open import Function.Equality using ( Π ; _⟶_ ; _⟨$⟩_ ; cong ; id ; _∘_ )
import Function.Inverse as Bas
open import Function using ( const ; _⟨_⟩_ )
open import Data.Unit using ( tt ) renaming ( setoid to ⊤-setoid )
open import Data.Product using ( _×_ ; proj₁ ; proj₂ ; _,′_ )
open import Relation.Binary.PropositionalEquality using () renaming ( refl to ≡-refl )

record Inverse {iℓ i≈ℓ aℓ a≈ℓ} (I-setoid : Setoid iℓ i≈ℓ) (A-setoid : Ix.Setoid (Setoid.Carrier I-setoid) aℓ a≈ℓ)
               {jℓ j≈ℓ bℓ b≈ℓ} (J-setoid : Setoid jℓ j≈ℓ) (B-setoid : Ix.Setoid (Setoid.Carrier J-setoid) bℓ b≈ℓ)
       : Set (iℓ ⊔ i≈ℓ ⊔ jℓ ⊔ j≈ℓ ⊔ aℓ ⊔ a≈ℓ ⊔ bℓ ⊔ b≈ℓ) where
  open    Setoid I-setoid using () renaming ( Carrier to  I
                                            ; _≈_     to _I≈_ )
  open    Setoid J-setoid using () renaming ( Carrier to  J
                                            ; _≈_     to _J≈_ )
  open Ix.Setoid A-setoid using () renaming ( Carrier to  A
                                            ; _≈_     to _A≈_ )
  open Ix.Setoid B-setoid using () renaming ( Carrier to  B
                                            ; _≈_     to _B≈_ )
  field
    to-index         : {v : I} → A-setoid at v ⟶ J-setoid
    from-index       : {w : J} → B-setoid at w ⟶ I-setoid
    to               : {v : I} → A-setoid at v ⟨ Π {aℓ} {a≈ℓ} {bℓ} {b≈ℓ} ⟩ B-setoid on _⟨$⟩_ to-index
    from             : {w : J} → B-setoid at w ⟨ Π {bℓ} {b≈ℓ} {aℓ} {a≈ℓ} ⟩ A-setoid on _⟨$⟩_ from-index
    left-inverse-of  : {v : I} (x : A v) → (from-index ⟨$⟩ (to   ⟨$⟩ x) I≈ v) × (from ⟨$⟩ (to   ⟨$⟩ x) A≈ x)
    right-inverse-of : {w : J} (y : B w) → (to-index   ⟨$⟩ (from ⟨$⟩ y) J≈ w) × (to   ⟨$⟩ (from ⟨$⟩ y) B≈ y)

makeDependent : ∀{aℓ a≈ℓ bℓ b≈ℓ} {A-setoid : Setoid aℓ a≈ℓ}
                  {B-setoid : Setoid bℓ b≈ℓ} →
                  Bas.Inverse A-setoid B-setoid →
                  Inverse ⊤-setoid (Setoid.indexedSetoid A-setoid) ⊤-setoid
                  (Setoid.indexedSetoid B-setoid)
makeDependent inv = record {
                      to-index = record { _⟨$⟩_ = const tt; cong = const ≡-refl };
                      to =
                        λ {v} →
                          record {
                          _⟨$⟩_ = _⟨$⟩_ (Bas.Inverse.to inv);
                          cong = cong (Bas.Inverse.to inv) };
                      from-index = record { _⟨$⟩_ = const tt; cong = const ≡-refl };
                      from =
                        λ {w} →
                          record {
                          _⟨$⟩_ = _⟨$⟩_ (Bas.Inverse.from inv);
                          cong = cong (Bas.Inverse.from inv) };
                      left-inverse-of = λ x → ≡-refl ,′ Bas.Inverse.left-inverse-of inv x;
                      right-inverse-of =
                        λ y → ≡-refl ,′ Bas.Inverse.right-inverse-of inv y }

refl : ∀{iℓ i≈ℓ aℓ a≈ℓ} {I-setoid : Setoid iℓ i≈ℓ}
         {A-setoid : Ix.Setoid (Setoid.Carrier I-setoid) aℓ a≈ℓ} →
         Inverse I-setoid A-setoid I-setoid A-setoid
refl {_} {_} {_} {_} {I-setoid} {A-setoid} = record {
                                               to-index = λ {v} → record { _⟨$⟩_ = const v; cong = const I-refl };
                                               from-index =
                                                 λ {w} → record { _⟨$⟩_ = const w; cong = const I-refl };
                                               to = id;
                                               from = id;
                                               left-inverse-of = λ _ → I-refl ,′ A-refl;
                                               right-inverse-of = λ _ → I-refl ,′ A-refl }
  where
    open    Setoid I-setoid using () renaming ( refl to I-refl )
    open Ix.Setoid A-setoid using () renaming ( refl to A-refl )

sym : ∀{iℓ i≈ℓ aℓ a≈ℓ} {I-setoid : Setoid iℓ i≈ℓ}
        {A-setoid : Ix.Setoid (Setoid.Carrier I-setoid) aℓ a≈ℓ} →
        ∀{jℓ j≈ℓ bℓ b≈ℓ} {J-setoid : Setoid jℓ j≈ℓ}
        {B-setoid : Ix.Setoid (Setoid.Carrier J-setoid) bℓ b≈ℓ} →
        Inverse I-setoid A-setoid J-setoid B-setoid →
        Inverse J-setoid B-setoid I-setoid A-setoid
sym inv = record {
            to-index = Inverse.from-index inv;
            from-index = Inverse.to-index inv;
            to = Inverse.from inv;
            from = Inverse.to inv;
            left-inverse-of = Inverse.right-inverse-of inv;
            right-inverse-of = Inverse.left-inverse-of inv }    
