{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Sum.Properties where

open import Cubical.Data.Empty
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary

open import Operad.Sum.Base

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    A : Type ℓ₁
    B : Type ℓ₂
    C : Type ℓ₃
    D : Type ℓ₄
    E : Type ℓ₅

  case⊎ : (x y : C) → A ⊎ B → C
  case⊎ x y (inl _) = x
  case⊎ x y (inr _) = y

[,]-map-commute : {f : A → B}  {g : C → D}
                  {f′ : B → E} {g′ : D → E} →
                  (x : A ⊎ C) → [ f′ , g′ ] (map f g x) ≡ [ f′ ∘ f , g′ ∘ g ] x
[,]-map-commute (inl x) = refl
[,]-map-commute (inr x) = refl

[,]-left-commute : {f : A → B} {f′ : B → D} {g : C → D} →
                   (x : A ⊎ C) → [ f′ , g ] (left f x) ≡ [ f′ ∘ f , g ] x
[,]-left-commute (inl x) = refl
[,]-left-commute (inr x) = refl

[,]-∘-distr : (f : C → D) {g : A → C} {h : B → C} →
              (x : A ⊎ B) → f ([ g , h ] x) ≡ [ f ∘ g , f ∘ h ] x
[,]-∘-distr _ (inl _) = refl
[,]-∘-distr _ (inr _) = refl

inl-inj : {x y : A} → inl {B = B} x ≡ inl y → x ≡ y
inl-inj {x = x} {y = y} = lower ∘ SumPath.encode (inl x) (inl y)

inr-inj : {x y : B} → inr {A = A} x ≡ inr y → x ≡ y
inr-inj {x = x} {y = y} = lower ∘ SumPath.encode (inr x) (inr y)

inl≢inr : {x : A} {y : B} → ¬ (inl {A = A} x ≡ inr {B = B} y)
inl≢inr p = subst (case⊎ ⊤ ⊥) p _
