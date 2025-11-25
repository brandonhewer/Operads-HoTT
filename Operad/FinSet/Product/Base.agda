{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Product.Base where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Sigma

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.FinSet.Properties

open Iso

private
  variable
    ℓ₁ ℓ₂ : Level

  ΣFin↔FinΣ′ : ∀ m ns → Iso (Σ[ a ∈ Lift {j = ℓ₁} (Fin m) ] Lift {j = ℓ₂} (Fin (ns (lower a))))
                            (Fin (ΣFin m ns))
  ΣFin↔FinΣ′ m ns = compIso (iso (λ { (i , j) → lower i , lower j })
                                 (λ { (i , j) → lift i , lift j })
                                 (λ { (i , j) → refl })
                                 (λ { (i , j) → refl }))
                            (ΣFin↔FinΣ m ns)

  ×Fin↔Fin*′ : ∀ m n → Iso (Lift {j = ℓ₁} (Fin m) × Lift {j = ℓ₂} (Fin n)) (Fin (m * n))
  ×Fin↔Fin*′ m n = compIso (prodIso (invIso LiftIso) (invIso LiftIso)) (×Fin↔Fin* m n)

isFiniteΣ : {A : Type ℓ₁} {B : A → Type ℓ₂} →
            isFinite A → ((a : A) → isFinite (B a)) → isFinite (Σ A B)
isFiniteΣ isFiniteA isFiniteB =
  isFiniteClosure Σ ΣFin ΣFin↔FinΣ′ isFiniteA isFiniteB

isFinite× : {A : Type ℓ₁} {B : Type ℓ₂} → isFinite A → isFinite B → isFinite (A × B)
isFinite× isFiniteA isFiniteB =
  isFiniteClosure′ _×_ _*_ ×Fin↔Fin*′ isFiniteA isFiniteB

Σⁿ : (A : FinSet ℓ₁) (B : ⟦ A ⟧ → FinSet ℓ₂) → FinSet (ℓ-max ℓ₁ ℓ₂)
Σⁿ = fromClosure Σ ΣFin ΣFin↔FinΣ′

_×ⁿ_ : FinSet ℓ₁ → FinSet ℓ₂ → FinSet (ℓ-max ℓ₁ ℓ₂)
_×ⁿ_ = fromClosure′ _×_ _*_ ×Fin↔Fin*′
