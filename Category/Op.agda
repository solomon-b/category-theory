{-# OPTIONS --type-in-type #-}
module Category.Op where

import Relation.Binary.PropositionalEquality as Eq
open import Relation.Binary

open import Category
open Equiv

------------------------------------------------------------------------------------------
-- The Opposite Category

Op : (π : Category) β Category
ob (Op π) = ob π
hom (Op π) = Ξ» x y β hom π y x
id (Op π) = id π
_β¨_ (Op π) = Ξ» f g β π [ g β¨ f ]
_β_ (Op π) = Ξ» f g β π [ f β g ]
cong-β¨ (Op π) = Ξ» fβh gβi β cong-β¨ π gβi fβh
unitα΅£ (Op π) = unitβ π
unitβ (Op π) = unitα΅£ π
assoc (Op π) = Ξ» f g h β sym π (assoc π h g f)
isEquivalence (Op π) = isEquivalence π
