{-# OPTIONS --type-in-type #-}
module Isomorphism where

open import Relation.Binary.PropositionalEquality using (_β‘_)
open import Category

------------------------------------------------------------------------------------------
-- Isomorphisms

infix 0 _β_
record _β_ (π : Category) (A B : ob π) : Set where
  field
    to   : π [ A , B ]
    from : π [ B , A ]
    fromβ¨to : π [ π [ from β¨ to ] β id π B ]
    toβ¨from : π [ π [ to β¨ from ] β id π A ]
open _β_ public

infix 5 _[_β_]
_[_β_] : (π : Category) β ( A B : ob π ) β Set
_[_β_] π A B = _β_ π A B
