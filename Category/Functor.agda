{-# OPTIONS --type-in-type #-}
module Category.Functor where

------------------------------------------------------------------------------------------

open import Category
open import Category.Sets
open import Functor
open import FunExt
open import NaturalTransformation

------------------------------------------------------------------------------------------
-- The Category of Functors where morphisms are Natural Transformations.

compose : {𝒞 𝒟 : Category} → {F₀ F₁ F₂ : Functor 𝒞 𝒟} → NaturalTransformation F₀ F₁ → NaturalTransformation F₁ F₂ → NaturalTransformation F₀ F₂
η (compose {𝒞} {𝒟} {F₀} {F₁} {F₂} α β) X = 𝒟 [ α .η X ⨟ β .η X ]
commute (compose {𝒞} {𝒟} {F₀} {F₁} {F₂} α β) {X} {Y} f = begin
  𝒟 [ mapₘ F₀ f ⨟ 𝒟 [ α .η Y ⨟ β .η Y ] ]
       ≈⟨ 𝒟 .assoc _ _ _ ⟩
  𝒟 [ 𝒟 [ mapₘ F₀ f ⨟ α .η Y ] ⨟ β .η Y ] ≈⟨ cong-⨟ 𝒟 (α .commute f) (Equiv.refl 𝒟) ⟩
  𝒟 [ 𝒟 [ η α X ⨟ mapₘ F₁ f ] ⨟ β .η Y ] ≈⟨ Equiv.sym 𝒟 (𝒟 .assoc _ _ _) ⟩
  𝒟 [ η α X ⨟ 𝒟 [ mapₘ F₁ f ⨟ β .η Y ] ] ≈⟨ cong-⨟ 𝒟 (Equiv.refl 𝒟) (β .commute f) ⟩
  𝒟 [ η α X ⨟ 𝒟 [ β .η X ⨟ mapₘ F₂ f ] ] ≈⟨ 𝒟 .assoc _ _ _ ⟩
  𝒟 [ 𝒟 [ α .η X ⨟ β .η X ] ⨟ mapₘ F₂ f ] ∎
  where open Reasoning 𝒟

id-nat : ∀ {𝒞 𝒟 : Category} → (F : Functor 𝒞 𝒟) → NaturalTransformation F F
η (id-nat {𝒟 = 𝒟} F) X = 𝒟 .id (mapₒ F X)
commute (id-nat {𝒟 = 𝒟} F) f = Equiv.trans 𝒟 (𝒟 .unitᵣ _) (Equiv.sym 𝒟 (𝒟 .unitₗ _))

FunctorCategory : (𝒞 : Category) → (𝒟 : Category) → Category
ob (FunctorCategory 𝒞 𝒟) = Functor 𝒞 𝒟
hom (FunctorCategory 𝒞 𝒟) = NaturalTransformation
id (FunctorCategory 𝒞 𝒟) = id-nat
_⨟_ (FunctorCategory 𝒞 𝒟) = compose
_≈_ (FunctorCategory 𝒞 𝒟) = λ f g → ∀ X → 𝒟 [ η f X ≈ η g X ]
unitᵣ (FunctorCategory 𝒞 𝒟) {F} {G} = λ α X → 𝒟 .unitᵣ _
  -- begin
  -- 𝒟 [ α .η X ⨟ G .mapₘ (id 𝒞 X) ] ≈⟨ cong-⨟ 𝒟 (Equiv.refl 𝒟) (G .id) ⟩
  -- 𝒟 [ α .η X ⨟ 𝒟 .id _ ] ≈⟨ 𝒟 .unitᵣ _ ⟩
  -- α .η X
  -- ∎
  -- where open Reasoning 𝒟
unitₗ (FunctorCategory 𝒞 𝒟) {F} {G} = λ α X → 𝒟 .unitₗ _
  -- begin
  -- 𝒟 [ F .mapₘ (id 𝒞 X) ⨟ α .η X ] ≈⟨ cong-⨟ 𝒟 (F .id) (Equiv.refl 𝒟) ⟩
  -- 𝒟 [ 𝒟 .id _ ⨟ α .η X ] ≈⟨ 𝒟 .unitₗ _ ⟩
  -- α .η X
  -- ∎
  -- where open Reasoning 𝒟
assoc (FunctorCategory 𝒞 𝒟) = λ f g h X → 𝒟 .assoc _ _ _
isEquivalence (FunctorCategory 𝒞 𝒟) = record { refl = λ c → Equiv.refl 𝒟 ; sym = λ p x → Equiv.sym 𝒟 (p x) ; trans = λ p q x → Equiv.trans 𝒟 (p x) (q x) }
cong-⨟ (FunctorCategory 𝒞 𝒟) = λ prf₁ prf₂ X → cong-⨟ 𝒟 (prf₁ X) (prf₂ X)
