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
    ; id = λ f → refl
    ; composition = λ f → refl
    ; cong-mapₘ = λ prf f → ∀-extensionality (λ x → prf (f x))
    }
