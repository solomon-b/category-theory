{-# OPTIONS --type-in-type #-}
module NaturalTransformation where

open import Category
open import Functor
open import Relation.Binary
open import Isomorphism

record NaturalTransformation
  {𝒞 : Category} {𝒟 : Category} (F G : Functor 𝒞 𝒟) : Set where
  field
    η : ∀ X → 𝒟 [ mapₒ F X , mapₒ G X ]
    commute : ∀ {X Y} (f : 𝒞 [ X , Y ]) → 𝒟 [ 𝒟 [ mapₘ F f ⨟ η Y ] ≈ 𝒟 [ η X ⨟ mapₘ G f ] ]

open NaturalTransformation public

infix 4 _≃_

_≃_ : ∀ {C D : Category} {F G : Functor C D} → Rel (NaturalTransformation F G) _
_≃_ {D = D} X Y = ∀ {x} → D [ η X x ≈ η Y x ]


≃-isEquivalence : ∀ {C D : Category} {F G : Functor C D} → IsEquivalence (_≃_ {F = F} {G})
≃-isEquivalence {D = D} {F} {G} = record
  { refl  = refl
  ; sym   = λ f → sym f -- need to eta-expand to get things to line up properly
  ; trans = λ f g → trans f g
  }
  where open Category.Equiv D
