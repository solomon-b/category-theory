module FunExt where

open import Relation.Binary.PropositionalEquality using (_≡_)

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g
