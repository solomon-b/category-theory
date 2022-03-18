{-# OPTIONS --type-in-type #-}
module NaturalTransformation where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Category
open import Functor
open import Isomorphism

record NaturalTransformation
  {𝒞 : Category} {𝒟 : Category} (F G : Functor 𝒞 𝒟) : Set where
  field
    η : ∀ X → 𝒟 [ mapₒ F X , mapₒ G X ]
    commute : ∀ {X Y} (f : 𝒞 [ X , Y ]) → 𝒟 [ mapₘ F f ⨟ η Y ] ≡ 𝒟 [ η X ⨟ mapₘ G f ]
