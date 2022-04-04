{-# OPTIONS --type-in-type #-}
module Category.Sets where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans)
open import Relation.Binary

open import Category

------------------------------------------------------------------------------------------
-- The Category of Sets where morphisms are functions

Sets : Category
ob    Sets = Set
hom   Sets = λ A B → (A → B)
id    Sets = λ _ x → x
_⨟_   Sets = λ f g x → g (f x)
_≈_   Sets = λ f g → ∀ x → f x ≡ g x
unitᵣ Sets = λ f x → refl
unitₗ Sets = λ f x → refl
assoc Sets = λ f g h x → refl
cong-⨟ Sets {f = f} {i = i} = λ p q x → trans (q (f x)) (cong i (p x))
IsEquivalence.refl (isEquivalence Sets) = λ x → refl
IsEquivalence.sym (isEquivalence Sets) = λ prf x → sym (prf x)
IsEquivalence.trans (isEquivalence Sets) = λ prf1 prf2 x → trans (prf1 x) (prf2 x)
