{-# OPTIONS --type-in-type #-}
module Representable where

open import Category
open import Functor
open import Isomorphism

------------------------------------------------------------------------------------------
-- Representable

record Representable (ð : Category ) (F : Functor ð Sets) : Set where
  field
    rep : ob ð
    iso : { a : ob ð } â Sets [ mapâ F a â ð [ rep , a ] ]

open Representable public
