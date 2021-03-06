{-# OPTIONS --type-in-type #-}
module Functor where

open import Relation.Binary.PropositionalEquality using (_â¡_)
open import Category
open import Isomorphism

------------------------------------------------------------------------------------------
-- Definition

record Functor (ð : Category) (ð : Category) : Set where
  field
    mapâ : ob ð â ob ð
    mapâ : { x y : ob ð } â ð [ x , y ]  â ð [ mapâ x , mapâ y ]
    id : { x : ob ð } â ð [ mapâ (id ð x) â id ð (mapâ x) ]
    composition : { x y z : ob ð } â { f : ð [ y , z ] } â { g : ð [ x , y ] } â ð [ mapâ (ð [ g â¨ f ]) â ð [ mapâ g â¨ mapâ f ] ]
    cong-mapâ : â {X Y : ob ð} â {f g : hom ð X Y} â ð [ f â g ] â ð [ mapâ f â mapâ g ]

open Functor public

EndoFunctor : (ð : Category) â Set
EndoFunctor ð = Functor ð ð
