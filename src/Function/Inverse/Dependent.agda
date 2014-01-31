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
open import Function using ( const ; _⟨_⟩_ ; _⟨′_‵⟩_ ; _∋_ ; ∋-syntax )
open import Data.Unit using ( ⊤ ; tt ) renaming ( setoid to ⊤-setoid )
open import Data.Product using ( _×_ ; proj₁ ; proj₂ ; _,_ ; _,′_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ ; subst ; subst-eq ) renaming ( refl to ≡-refl ; setoid to ≡-setoid )

record Inverse {iℓ aℓ a≈ℓ} {I : Set iℓ} (A-setoid : Ix.Setoid I aℓ a≈ℓ)
               {jℓ bℓ b≈ℓ} {J : Set jℓ} (B-setoid : Ix.Setoid J bℓ b≈ℓ)
       : Set (iℓ ⊔ aℓ ⊔ a≈ℓ ⊔ jℓ ⊔ bℓ ⊔ b≈ℓ) where
  open Ix.Setoid A-setoid using () renaming ( Carrier to  A
                                            ; _≈_     to _A≈_ )
  open Ix.Setoid B-setoid using () renaming ( Carrier to  B
                                            ; _≈_     to _B≈_ )
  field
    to-index         : {v : I} → A-setoid at v ⟶ ≡-setoid J
    from-index       : {w : J} → B-setoid at w ⟶ ≡-setoid I
    to               : {v : I} → A-setoid at v ⟨ Π {aℓ} {a≈ℓ} {bℓ} {b≈ℓ} ⟩ B-setoid on _⟨$⟩_ to-index
    from             : {w : J} → B-setoid at w ⟨ Π {bℓ} {b≈ℓ} {aℓ} {a≈ℓ} ⟩ A-setoid on _⟨$⟩_ from-index
    left-inverse-of  : {v : I} (x : A v) → (from-index ⟨$⟩ (to   ⟨$⟩ x) ≡ v) × (from ⟨$⟩ (to   ⟨$⟩ x) A≈ x)
    right-inverse-of : {w : J} (y : B w) → (to-index   ⟨$⟩ (from ⟨$⟩ y) ≡ w) × (to   ⟨$⟩ (from ⟨$⟩ y) B≈ y)

makeDependent : ∀{aℓ a≈ℓ bℓ b≈ℓ} {A-setoid : Setoid aℓ a≈ℓ}
                  {B-setoid : Setoid bℓ b≈ℓ} →
                  Bas.Inverse A-setoid B-setoid →
                  Inverse (Setoid.indexedSetoid A-setoid {I = ⊤})
                  (Setoid.indexedSetoid B-setoid {I = ⊤})
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
                      left-inverse-of =
                        λ x → ≡-refl ,′ Bas.Inverse.left-inverse-of inv x;
                      right-inverse-of =
                        λ y → ≡-refl ,′ Bas.Inverse.right-inverse-of inv y }

refl : ∀{iℓ aℓ a≈ℓ} {I : Set iℓ}
         {A-setoid : Ix.Setoid I aℓ a≈ℓ} →
         Inverse A-setoid A-setoid
refl {_} {_} {_} {I} {A-setoid} = record {
                                    to-index = λ {v} → record { _⟨$⟩_ = const v; cong = const ≡-refl };
                                    from-index =
                                      λ {w} → record { _⟨$⟩_ = const w; cong = const ≡-refl };
                                    to = id;
                                    from = id;
                                    left-inverse-of = λ _ → ≡-refl ,′ A-refl;
                                    right-inverse-of = λ _ → ≡-refl ,′ A-refl }
  where
    open Ix.Setoid A-setoid using () renaming ( refl to A-refl )

sym : ∀{iℓ aℓ a≈ℓ} {I : Set iℓ}
        {A-setoid : Ix.Setoid I aℓ a≈ℓ}
        {jℓ bℓ b≈ℓ} {J : Set jℓ}
        {B-setoid : Ix.Setoid J bℓ b≈ℓ} →
        Inverse A-setoid B-setoid → Inverse B-setoid A-setoid
sym inv = record {
            to-index = Inverse.from-index inv;
            from-index = Inverse.to-index inv;
            to = Inverse.from inv;
            from = Inverse.to inv;
            left-inverse-of = Inverse.right-inverse-of inv;
            right-inverse-of = Inverse.left-inverse-of inv }

{-
trans : ∀{iℓ aℓ a≈ℓ} {I : Set iℓ} {A-setoid : Ix.Setoid I aℓ a≈ℓ}
          {jℓ bℓ b≈ℓ} {J : Set jℓ} {B-setoid : Ix.Setoid J bℓ b≈ℓ}
          {kℓ cℓ c≈ℓ} {K : Set kℓ} {C-setoid : Ix.Setoid K cℓ c≈ℓ} →
          Inverse A-setoid B-setoid →
          Inverse B-setoid C-setoid → Inverse A-setoid C-setoid
-}
