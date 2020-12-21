{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Species.Base where

open import Cubical.Data.Nat

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary

open import Operad.FinSet
open import Operad.Sum

PointedSpecies : ∀ {ℓ₁} ℓ₂ → HLevel → ℕ → FinSet ℓ₁ → Type _
PointedSpecies ℓ₂ i n X = Σ[ A ∈ TypeOfHLevel ℓ₂ i ] (n ≡ card X → typ A)

PointedSpecies′ : ∀ {ℓ₁} ℓ₂ → ℕ → FinSet ℓ₁ → Type _
PointedSpecies′ ℓ₂ n X = Σ[ A ∈ Type ℓ₂ ] (n ≡ card X → A)

Species : HLevel → ∀ ℓ₁ ℓ₂ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
Species n ℓ₁ ℓ₂ = FinSet ℓ₁ → TypeOfHLevel ℓ₂ n

*Species : HLevel → ∀ ℓ₁ ℓ₂ → ℕ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
*Species m ℓ₁ ℓ₂ n = (X : FinSet ℓ₁) → PointedSpecies ℓ₂ m n X

*Species′ : ∀ ℓ₁ ℓ₂ → ℕ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
*Species′ ℓ₁ ℓ₂ n = (X : FinSet ℓ₁) → PointedSpecies′ ℓ₂ n X
