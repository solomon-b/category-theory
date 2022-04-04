module FunExt where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

postulate
  ∀-extensionality : ∀ {A : Set} {B : A → Set} {f g : ∀(x : A) → B x} → (∀ (x : A) → f x ≡ g x) → f ≡ g

uip : {A : Set} -> {x y : A} -> (p q : x ≡ y) -> p ≡ q
uip refl refl = refl
