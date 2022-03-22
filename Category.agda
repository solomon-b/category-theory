{-# OPTIONS --type-in-type #-}
module Category where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; cong; refl; sym)

open import FunExt

------------------------------------------------------------------------------------------
-- Category

record Category : Set where
  field
    ob : Set
    hom : ob → ob → Set
    id : (x : ob) → hom x x
    _⨟_ : { x y z : ob } → hom x y → hom y z → hom x z

    unitᵣ : { x y : ob } → (f : hom x y) → f ⨟ id y ≡ f
    unitₗ : { x y : ob } → (f : hom x y) → id x ⨟ f ≡ f
    assoc : { x y z h : ob } → (f : hom x y) → (g : hom y z) → (h : hom z h) → f ⨟ (g ⨟ h) ≡ (f ⨟ g) ⨟ h

open Category public

infix 5 _[_∘_]
_[_∘_] : (𝒞 : Category) { x y z : ob 𝒞 } → hom 𝒞 y z → hom 𝒞 x y → hom 𝒞 x z
_[_∘_] 𝒞 f g = _⨟_ 𝒞 g f

infix 5 _[_,_]
_[_,_] : (𝒞 : Category) → ob 𝒞 → ob 𝒞 → Set
𝒞 [ X , Y ] = hom 𝒞 X Y

infix 5 _[_⨟_]
_[_⨟_] : (𝒞 : Category) → { X Y Z : ob 𝒞 } → 𝒞 [ X , Y ] → 𝒞 [ Y , Z ] → 𝒞 [ X , Z ]
_[_⨟_] 𝒞 f g = _⨟_ 𝒞 f g

-- | The Category of Sets
Sets : Category
ob    Sets = Set
hom   Sets = λ A B → (A → B)
id    Sets = λ _ x → x
_⨟_   Sets = λ f g x → g (f x)
unitᵣ Sets = λ f → refl
unitₗ Sets = λ f → refl
assoc Sets = λ f g h → refl

-- | The Opposite Category
Op : (𝒞 : Category) → Category
Op 𝒞 =
  record
    { ob = ob 𝒞
    ; hom = λ x y → hom 𝒞 y x
    ; id =  id 𝒞
    ; _⨟_ = λ f g → 𝒞 [ g ⨟ f ]
    ; unitᵣ = unitₗ 𝒞
    ; unitₗ = unitᵣ 𝒞
    ; assoc = λ f g h → sym (assoc 𝒞 h g f)
    }

