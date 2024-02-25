{-# OPTIONS --type-in-type #-}
module Category where

import Relation.Binary.PropositionalEquality as Eq
import Relation.Binary.Reasoning.Setoid

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

  HomSetoid : ∀ (X Y : ob) → Setoid _ _
  Setoid.Carrier (HomSetoid X Y) = hom X Y
  Setoid._≈_ (HomSetoid X Y) = _≈_
  Setoid.isEquivalence (HomSetoid X Y) = isEquivalence

  module Equiv {A B : ob} = IsEquivalence (isEquivalence {A} {B})
  module Reasoning {X Y : ob} = Relation.Binary.Reasoning.Setoid (HomSetoid X Y)

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
