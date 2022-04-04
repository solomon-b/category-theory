{-# OPTIONS --type-in-type #-}
module Category where

import Relation.Binary.PropositionalEquality as Eq
--open Eq using (_≡_; cong; refl; sym; trans)

open import Relation.Binary
open import FunExt

------------------------------------------------------------------------------------------
-- Category

record Category : Set where
  infix 4 _≈_
  infixr 9 _⨟_
  field
    ob : Set
    hom : ob → ob → Set
    id : (x : ob) → hom x x
    _⨟_ : { x y z : ob } → hom x y → hom y z → hom x z
    _≈_ : {x y : ob} → (f g : hom x y) → Set

    unitᵣ : { x y : ob } → (f : hom x y) → f ⨟ id y ≈ f
    unitₗ : { x y : ob } → (f : hom x y) → id x ⨟ f ≈ f
    assoc : { x y z h : ob } → (f : hom x y) → (g : hom y z) → (h : hom z h) → f ⨟ (g ⨟ h) ≈ (f ⨟ g) ⨟ h

    isEquivalence : ∀ {X Y} → IsEquivalence (_≈_ {X} {Y})
    cong-⨟ : ∀ {X Y Z} → {f h : hom X Y} → {g i : hom Y Z} → f ≈ h → g ≈ i → f ⨟ g ≈ h ⨟ i

  module Equiv {A B : ob} = IsEquivalence (isEquivalence {A} {B}) 

open Category public
open Equiv

infix 5 _[_∘_]
_[_∘_] : (𝒞 : Category) { x y z : ob 𝒞 } → hom 𝒞 y z → hom 𝒞 x y → hom 𝒞 x z
_[_∘_] 𝒞 f g = _⨟_ 𝒞 g f

infix 5 _[_,_]
_[_,_] : (𝒞 : Category) → ob 𝒞 → ob 𝒞 → Set
𝒞 [ X , Y ] = hom 𝒞 X Y

infix 5 _[_⨟_]
_[_⨟_] : (𝒞 : Category) → { X Y Z : ob 𝒞 } → 𝒞 [ X , Y ] → 𝒞 [ Y , Z ] → 𝒞 [ X , Z ]
_[_⨟_] 𝒞 f g = _⨟_ 𝒞 f g

infix 5 _[_≈_]
_[_≈_] : (𝒞 : Category) → {x y : ob 𝒞} → (f g : hom 𝒞 x y) → Set
_[_≈_] 𝒞 f g = _≈_ 𝒞 f g

-- | The Category of Sets
Sets : Category
ob    Sets = Set
hom   Sets = λ A B → (A → B)
id    Sets = λ _ x → x
_⨟_   Sets = λ f g x → g (f x)
_≈_   Sets = λ f g → ∀ x → f x Eq.≡ g x
unitᵣ Sets = λ f x → Eq.refl
unitₗ Sets = λ f x → Eq.refl
assoc Sets = λ f g h x → Eq.refl
cong-⨟ Sets {f = f} {i = i} = λ p q x → Eq.trans (q (f x)) (Eq.cong i (p x))
IsEquivalence.refl (isEquivalence Sets) = λ x → Eq.refl
IsEquivalence.sym (isEquivalence Sets) = λ prf x → Eq.sym (prf x)
IsEquivalence.trans (isEquivalence Sets) = λ prf1 prf2 x → Eq.trans (prf1 x) (prf2 x)

-- | The Opposite Category
Op : (𝒞 : Category) → Category
ob (Op 𝒞) = ob 𝒞
hom (Op 𝒞) = λ x y → hom 𝒞 y x
id (Op 𝒞) = id 𝒞
_⨟_ (Op 𝒞) = λ f g → 𝒞 [ g ⨟ f ]
_≈_ (Op 𝒞) = λ f g → 𝒞 [ f ≈ g ]
cong-⨟ (Op 𝒞) = λ f≈h g≈i → cong-⨟ 𝒞 g≈i f≈h
unitᵣ (Op 𝒞) = unitₗ 𝒞
unitₗ (Op 𝒞) = unitᵣ 𝒞
assoc (Op 𝒞) = λ f g h → sym 𝒞 (assoc 𝒞 h g f)
isEquivalence (Op 𝒞) = isEquivalence 𝒞
