{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Product.Properties where

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.FinSet.Product.Base
open import Operad.FinSet.Properties
open import Operad.Sigma

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Type ℓ₁

Σⁿ-Idl : {A : FinSet ℓ₁} → (Σⁿ (1-FinSet ℓ₁) λ _ → A) ≡ A
Σⁿ-Idl = Lift≡ _ _ (isoToPath Σ-Idl)

Σⁿ-Idr : {A : FinSet ℓ₁} → (Σⁿ A λ _ → 1-FinSet ℓ₁) ≡ A
Σⁿ-Idr = Lift≡ _ _ (isoToPath Σ-Idr)

Σⁿ-Assoc : (A : FinSet ℓ₁)
           (B : ⟦ A ⟧ → FinSet ℓ₂)
           (C : (a : ⟦ A ⟧) → ⟦ B a ⟧ → FinSet ℓ₃) →
           (Σⁿ (Σⁿ A B) (uncurry C)) ≡ (Σⁿ A λ a → Σⁿ (B a) (C a))
Σⁿ-Assoc _ _ _ = Lift≡ _ _ (isoToPath Σ-assoc-Iso)

