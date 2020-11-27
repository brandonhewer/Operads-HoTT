{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Species.Base where

open import Cubical.Data.Nat

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Operad.FinSet

Species : HLevel → ∀ ℓ₁ ℓ₂ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
Species n ℓ₁ ℓ₂ = FinSet ℓ₁ → TypeOfHLevel ℓ₂ n

*Species : HLevel → ∀ ℓ₁ ℓ₂ → ℕ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
*Species m ℓ₁ ℓ₂ n = (X : FinSet ℓ₁) → Σ[ A ∈ TypeOfHLevel ℓ₂ m ] (n ≡ card X → typ A)

*Species′ : ∀ ℓ₁ ℓ₂ → ℕ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
*Species′ ℓ₁ ℓ₂ n = (X : FinSet ℓ₁) → Σ[ A ∈ Type ℓ₂ ] (n ≡ card X → A)
