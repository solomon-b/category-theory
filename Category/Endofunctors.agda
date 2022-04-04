{-# OPTIONS --type-in-type #-}
module Category.Endofunctors where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; trans; module ≡-Reasoning)
open ≡-Reasoning
open import Relation.Binary

open import Category
open import Functor
open import FunExt
open import NaturalTransformation


compose : {F₀ F₁ F₂ : EndoFunctor Sets} → NaturalTransformation F₀ F₁ → NaturalTransformation F₁ F₂ → NaturalTransformation F₀ F₂
compose {Fₒ} {F₁} {F₂} record { η = ηˣʸ ; commute = c¹ } record { η = ηʸᶻ ; commute = c² } =
  record { η = λ X mapₒˣ → ηʸᶻ X (ηˣʸ X mapₒˣ)
         ; commute = λ f → λ mapₒˣ →
             begin
               ηʸᶻ _ (ηˣʸ _ (mapₘ Fₒ f mapₒˣ))
             ≡⟨ cong (ηʸᶻ _) (c¹ f mapₒˣ) ⟩
               ηʸᶻ _ (mapₘ F₁ f (ηˣʸ _ mapₒˣ))
             ≡⟨ c² f (ηˣʸ _ mapₒˣ) ⟩
               mapₘ F₂ f (ηʸᶻ _ (ηˣʸ _ mapₒˣ))
             ∎
         }

EndoFunctorCategory : Category
ob EndoFunctorCategory = EndoFunctor Sets
hom EndoFunctorCategory = NaturalTransformation
id EndoFunctorCategory _ = record { η = λ _ mapₒᶠˣ → mapₒᶠˣ ; commute = λ _ _ → refl }
_⨟_ EndoFunctorCategory = compose 
_≈_ EndoFunctorCategory = λ f g → ∀ X → Sets [ η f X ≈ η g X ]
cong-⨟ EndoFunctorCategory = λ prf1 prf2 X mapₒ → cong-⨟ Sets (prf1 X) (prf2 X) mapₒ
unitᵣ EndoFunctorCategory = λ natˣʸ → λ _ _ → refl
unitₗ EndoFunctorCategory = λ natˣʸ →  λ _ _ → refl
assoc EndoFunctorCategory = λ f g h → λ _ _ → refl
IsEquivalence.refl (isEquivalence EndoFunctorCategory) = λ X x₁ → refl
IsEquivalence.sym (isEquivalence EndoFunctorCategory) = λ prf X fx → sym (prf X fx)
IsEquivalence.trans (isEquivalence EndoFunctorCategory) = λ prf1 prf2 X fx → trans (prf1 X fx) (prf2 X fx)
