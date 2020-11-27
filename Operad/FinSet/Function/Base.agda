{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Function.Base where

open import Cubical.Data.Nat

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.FinSet.Properties

private
  variable
    ℓ₁ ℓ₂ : Level

  ΠFin↔FinΠ′ : ∀ m ns → Iso ((a : Lift {j = ℓ₁} (Fin m)) → (Lift {j = ℓ₂} ∘ Fin ∘ ns ∘ lower) a)
                            (Fin (ΠFin m ns))
  ΠFin↔FinΠ′ m ns = compIso (iso (λ f → lower ∘ f ∘ lift)
                                 (λ f → lift ∘ f ∘ lower)
                                 (λ _ → refl)
                                 (λ _ → refl))
                            (ΠFin↔FinΠ m ns)

  →Fin↔Fin^′ : ∀ m n → Iso (Lift {j = ℓ₁} (Fin m) → Lift {j = ℓ₂} (Fin n)) (Fin (n ^ m))
  →Fin↔Fin^′ m n = compIso (iso (λ f → lower ∘ f ∘ lift)
                                (λ f → lift ∘ f ∘ lower)
                                (λ _ → refl)
                                (λ _ → refl))
                           (→Fin↔Fin^ m n)

isFiniteΠ : {A : Type ℓ₁} {B : A → Type ℓ₂} →
            isFinite A → ((a : A) → isFinite (B a)) → isFinite ((a : A) → B a)
isFiniteΠ {B = B} isFiniteA isFiniteB =
  isFiniteClosure (λ _ B → ∀ a → B a) ΠFin ΠFin↔FinΠ′ isFiniteA λ _ → isFiniteB _

isFinite→ : {A : Type ℓ₁} {B : Type ℓ₂} →
            isFinite A → isFinite B → isFinite (A → B)
isFinite→ = isFiniteClosure′ (λ A B → (A → B)) (flip _^_) →Fin↔Fin^′

Πⁿ : (A : FinSet ℓ₁) (B : ⟦ A ⟧ → FinSet ℓ₂) → FinSet (ℓ-max ℓ₁ ℓ₂)
Πⁿ = fromClosure (λ _ B → ∀ a → B a) ΠFin ΠFin↔FinΠ′
