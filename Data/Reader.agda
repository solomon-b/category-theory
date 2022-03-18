{-# OPTIONS --type-in-type #-}
module Data.Reader where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Category
open import Functor
open import FunExt

ReaderFunctor : (R : Set) → EndoFunctor Sets
ReaderFunctor R =
  record
    { mapₒ = λ A → (R → A)
    ; mapₘ = λ f g r → f (g r)
    ; id = ∀-extensionality λ f → ∀-extensionality λ r → refl
    ; composition = ∀-extensionality λ f → refl
    }
