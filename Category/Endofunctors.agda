{-# OPTIONS --type-in-type #-}
module Category.Endofunctors where

open import Relation.Binary.PropositionalEquality using (_≡_; cong; refl; sym; module ≡-Reasoning)
open ≡-Reasoning

open import Category
open import Functor
open import FunExt
open import NaturalTransformation


compose : {F₀ F₁ F₂ : EndoFunctor Sets} → NaturalTransformation F₀ F₁ → NaturalTransformation F₁ F₂ → NaturalTransformation F₀ F₂
compose {Fₒ} {F₁} {F₂} record { η = ηˣʸ ; commute = c¹ } record { η = ηʸᶻ ; commute = c² } =
  record { η = λ X mapₒˣ → ηʸᶻ X (ηˣʸ X mapₒˣ)
         ; commute = λ f → ∀-extensionality λ mapₒˣ →
             begin
               (Sets [ mapₘ Fₒ f ⨟ (λ mapₒˣ₁ → ηʸᶻ _ (ηˣʸ _ mapₒˣ₁)) ]) mapₒˣ
             ≡⟨ cong (λ g → ηʸᶻ _ (g mapₒˣ)) (c¹ f) ⟩
               ηʸᶻ {!!} ((Sets [ ηˣʸ _ ⨟ mapₘ F₁ f ]) mapₒˣ)
             ≡⟨ cong (λ g → g (ηˣʸ _ mapₒˣ)) (c² f) ⟩
               (Sets [ ηʸᶻ _ ⨟ mapₘ F₂ f ]) (ηˣʸ _ mapₒˣ)
             ≡⟨⟩
               (Sets [ (λ mapₒˣ₁ → ηʸᶻ _ (ηˣʸ _ mapₒˣ₁)) ⨟ mapₘ F₂ f ]) mapₒˣ
             ∎
         }

EndoFunctorCategory : Category
ob EndoFunctorCategory = EndoFunctor Sets
hom EndoFunctorCategory = NaturalTransformation
id EndoFunctorCategory _ = record { η = λ _ mapₒᶠˣ → mapₒᶠˣ ; commute = λ _ → ∀-extensionality λ _ → refl }
_⨟_ EndoFunctorCategory = compose 
unitᵣ EndoFunctorCategory = λ natˣʸ →
  begin
    (EndoFunctorCategory ⨟ natˣʸ) (id EndoFunctorCategory _)
  ≡⟨ {!!} ⟩
    natˣʸ
  ∎
unitₗ EndoFunctorCategory = λ f → 
  begin
    (EndoFunctorCategory ⨟ id EndoFunctorCategory _) f
  ≡⟨ {!!} ⟩
    f
  ∎
assoc EndoFunctorCategory = {!!}
