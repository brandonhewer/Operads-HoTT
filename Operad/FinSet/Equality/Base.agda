{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Equality.Base where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Cubical.Relation.Nullary

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.FinSet.Function
open import Operad.FinSet.Product.Base
open import Operad.FinSet.Properties

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    W : Type ℓ₁
    X : Type ℓ₂
    Y : Type ℓ₃
    Z : Type ℓ₄

  open Iso

  isFiniteIso′ : isFinite X → isFinite Y →
                 isFinite (Σ[ f ∈ (X → Y) ] Σ[ g ∈ (Y → X) ] section f g × retract f g)
  isFiniteIso′ isFiniteX isFiniteY =
    isFiniteΣ (isFinite→ isFiniteX isFiniteY)
      λ _ → isFiniteΣ (isFinite→ isFiniteY isFiniteX)
              λ _ → isFinite× (isFiniteΠ isFiniteY λ _ → isFiniteFin≡ isFiniteY _ _)
                              (isFiniteΠ isFiniteX λ _ → isFiniteFin≡ isFiniteX _ _)

  Σ↔Iso : Iso (Σ[ f ∈ (X → Y) ] Σ[ g ∈ (Y → X) ] section f g × retract f g) (Iso X Y)
  fun Σ↔Iso (f , g , r , l)     = iso f g r l
  inv Σ↔Iso I                   = fun I , inv I , rightInv I , leftInv I
  fun (rightInv Σ↔Iso I i)      = fun I
  inv (rightInv Σ↔Iso I i)      = inv I
  rightInv (rightInv Σ↔Iso I i) = rightInv I
  leftInv (rightInv Σ↔Iso I i)  = leftInv I
  leftInv Σ↔Iso (f , g , r , l) = refl

  Π↔isEquiv : (f : X → Y) → Iso (∀ y → isContr (fiber f y)) (isEquiv f)
  equiv-proof (fun (Π↔isEquiv f) p)        = p
  inv (Π↔isEquiv f)                        = equiv-proof
  equiv-proof (rightInv (Π↔isEquiv f) e i) = equiv-proof e
  leftInv (Π↔isEquiv f) _                  = refl

isFiniteIsEquiv : isFinite X → isFinite Y → (f : X → Y) → isFinite (isEquiv f)
isFiniteIsEquiv isFiniteX isFiniteY f =
  subst isFinite (isoToPath (Π↔isEquiv f)) (
        isFiniteΠ isFiniteY
          λ _ → isFiniteΣ (isFiniteΣ isFiniteX
          λ _ → isFiniteFin≡ isFiniteY _ _)
          λ _ → isFiniteΠ (isFiniteΣ isFiniteX
          λ _ → isFiniteFin≡ isFiniteY _ _)
          λ _ → isFiniteFin≡ (isFiniteΣ isFiniteX
          λ _ → isFiniteFin≡ isFiniteY _ _) _ _)

isFinite≃ : isFinite X → isFinite Y → isFinite (X ≃ Y)
isFinite≃ A B = isFiniteΣ (isFiniteΠ A λ _ → B) λ _ → isFiniteIsEquiv A B _

isFinite≃→≡ : isFinite (X ≃ Y) → isFinite (X ≡ Y)
isFinite≃→≡ (n , I) = n , p-rec propTruncIsProp (∣_∣ ∘ compIso univalenceIso) I

isFinite≡ : isFinite X → isFinite Y → isFinite (X ≡ Y)
isFinite≡ A B = isFinite≃→≡ (isFinite≃ A B)

isFiniteIso : isFinite X → isFinite Y → isFinite (Iso X Y)
isFiniteIso isFiniteX isFiniteY =
  subst isFinite (isoToPath Σ↔Iso) (isFiniteIso′ isFiniteX isFiniteY)

_≃ⁿ_ : FinSet ℓ₁ → FinSet ℓ₂ → FinSet (ℓ-max ℓ₁ ℓ₂)
(_ , isFiniteA) ≃ⁿ (_ , isFiniteB) = _ , isFinite≃ isFiniteA isFiniteB

_≡ⁿ_ : FinSet ℓ₁ → FinSet ℓ₁ → FinSet (ℓ-suc ℓ₁)
(_ , isFiniteA) ≡ⁿ (_ , isFiniteB) = _ , isFinite≡ isFiniteA isFiniteB

Isoⁿ : FinSet ℓ₁ → FinSet ℓ₂ → FinSet (ℓ-max ℓ₁ ℓ₂)
Isoⁿ (A , isFiniteA) (B , isFiniteB) = _ , isFiniteIso isFiniteA isFiniteB
