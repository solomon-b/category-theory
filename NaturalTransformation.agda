{-# OPTIONS --type-in-type #-}
module NaturalTransformation where

open import Category
open import Functor
open import Isomorphism

record NaturalTransformation
  {ð : Category} {ð : Category} (F G : Functor ð ð) : Set where
  field
    Î· : â X â ð [ mapâ F X , mapâ G X ]
    commute : â {X Y} (f : ð [ X , Y ]) â ð [ ð [ mapâ F f â¨ Î· Y ] â ð [ Î· X â¨ mapâ G f ] ]

open NaturalTransformation public
