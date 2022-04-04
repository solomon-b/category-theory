{-# OPTIONS --type-in-type #-}
module Category.Op where

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary

open import Category
open Equiv

------------------------------------------------------------------------------------------
-- The Opposite Category

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
