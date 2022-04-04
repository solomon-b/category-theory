{-# OPTIONS --type-in-type #-}
module Representable where

open import Category
open import Category.Sets
open import Functor
open import Isomorphism

------------------------------------------------------------------------------------------
-- Representable

record Representable (𝒞 : Category ) (F : Functor 𝒞 Sets) : Set where
  field
    rep : ob 𝒞
    iso : { a : ob 𝒞 } → Sets [ mapₒ F a ≅ 𝒞 [ rep , a ] ]

open Representable public
