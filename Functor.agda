{-# OPTIONS --type-in-type #-}
module Functor where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Category
open import Isomorphism

------------------------------------------------------------------------------------------
-- Definition

record Functor (𝒞 : Category) (𝒟 : Category) : Set where
  field
    mapₒ : ob 𝒞 → ob 𝒟
    mapₘ : { x y : ob 𝒞 } → 𝒞 [ x , y ]  → 𝒟 [ mapₒ x , mapₒ y ]
    id : { x : ob 𝒞 } → mapₘ (id 𝒞 x) ≡ id 𝒟 (mapₒ x)
    composition : { x y z : ob 𝒞 } → { f : 𝒞 [ y , z ] } → { g : 𝒞 [ x , y ] } → mapₘ (𝒞 [ g ⨟ f ]) ≡ 𝒟 [ mapₘ g ⨟ mapₘ f ]

open Functor public

EndoFunctor : (𝒞 : Category) → Set
EndoFunctor 𝒞 = Functor 𝒞 𝒞
