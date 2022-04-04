{-# OPTIONS --type-in-type #-}
module Isomorphism where

open import Relation.Binary.PropositionalEquality using (_≡_)
open import Category

------------------------------------------------------------------------------------------
-- Isomorphisms

infix 0 _≅_
record _≅_ (𝒞 : Category) (A B : ob 𝒞) : Set where
  field
    to   : 𝒞 [ A , B ]
    from : 𝒞 [ B , A ]
    from⨟to : 𝒞 [ 𝒞 [ from ⨟ to ] ≈ id 𝒞 B ]
    to⨟from : 𝒞 [ 𝒞 [ to ⨟ from ] ≈ id 𝒞 A ]
open _≅_ public

infix 5 _[_≅_]
_[_≅_] : (𝒞 : Category) → ( A B : ob 𝒞 ) → Set
_[_≅_] 𝒞 A B = _≅_ 𝒞 A B
