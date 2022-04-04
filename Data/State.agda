{-# OPTIONS --type-in-type #-}
module Data.State where


open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl)
open import Category
open import Category.Sets
open import Functor
open import FunExt

open import Function using (case_of_)
open import Data.Product

------------------------------------------------------------------------------------------
-- State : S → (S , A)

StateFunctor : (S : Set) → EndoFunctor Sets
StateFunctor S =
  record
    { mapₒ = λ A → (S → (S × A))
    ; mapₘ = λ f run s →
       case run s of λ{ (s' , x) → s' , (f x) }
    ; id = λ _ → refl
    ; composition = λ _ → refl
    ; cong-mapₘ = λ prf f → ∀-extensionality (λ s →
        cong (λ y →  ( proj₁ (f s) , y )) (prf (proj₂ (f s))) )
    }
