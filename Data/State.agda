{-# OPTIONS --type-in-type #-}
module Data.State where


open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Category
open import Functor
open import FunExt

open import Function using (case_of_)
open import Data.Product

-- State : S → (S , A)
StateFunctor : (S : Set) → EndoFunctor Sets
StateFunctor S =
  record
    { mapₒ = λ A → (S → (S × A))
    ; mapₘ = λ f run s →
       case run s of λ{ (s' , x) → s' , (f x) }
    ; id = refl
    ; composition = refl
    }
