{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Product.Properties where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.FinSet.Product.Base
open import Operad.FinSet.Properties

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Type ℓ₁
    B : Type ℓ₂

  open Iso

  Σ-Idl : Iso (Σ[ i ∈ Lift {j = ℓ₂} (Fin 1) ] A) A
  fun      Σ-Idl (_         , a) = a
  inv      Σ-Idl              a  = lift zero , a
  rightInv Σ-Idl              _  = refl
  leftInv  Σ-Idl (lift zero , _) = refl

  Σ-Idr : Iso (Σ[ a ∈ A ] Lift {j = ℓ₂} (Fin 1)) A
  fun      Σ-Idr (a ,         _) = a
  inv      Σ-Idr              a  = a , lift zero
  rightInv Σ-Idr              _  = refl
  leftInv  Σ-Idr (_ , lift zero) = refl

Σⁿ-Idl : {A : FinSet ℓ₁} → (Σⁿ (⊤-FinSet ℓ₁) λ _ → A) ≡ A
Σⁿ-Idl = Lift≡ _ _ (isoToPath Σ-Idl)

Σⁿ-Idr : {A : FinSet ℓ₁} → (Σⁿ A λ _ → ⊤-FinSet ℓ₁) ≡ A
Σⁿ-Idr = Lift≡ _ _ (isoToPath Σ-Idr)

Σⁿ-Assoc : (A : FinSet ℓ₁)
           (B : ⟦ A ⟧ → FinSet ℓ₂)
           (C : (a : ⟦ A ⟧) → ⟦ B a ⟧ → FinSet ℓ₃) →
           (Σⁿ (Σⁿ A B) (uncurry C)) ≡ (Σⁿ A λ a → Σⁿ (B a) (C a))
Σⁿ-Assoc _ _ _ = Lift≡ _ _ (isoToPath Σ-assoc-Iso)
