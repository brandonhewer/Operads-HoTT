{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Base where

open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Operad.Fin

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level

isFinite : Type ℓ₁ → Type ℓ₁
isFinite X = Σ[ n ∈ ℕ ] ∥ Iso X (Fin n) ∥

FinSet : ∀ ℓ → Type (ℓ-suc ℓ)
FinSet ℓ = Σ[ A ∈ Type ℓ ] isFinite A

⟦_⟧ : FinSet ℓ₁ → Type ℓ₁
⟦_⟧ = fst

card : FinSet ℓ₁ → ℕ
card (_ , n , _) = n

Fin↔ : (A : FinSet ℓ₁) → ∥ Iso ⟦ A ⟧ (Fin (card A)) ∥
Fin↔ (_ , _ , p) = p

rec : (A : FinSet ℓ₁) {P : Type ℓ₂} → isProp P → (Iso ⟦ A ⟧ (Fin (card A)) → P) → P
rec (_ , _ , I) p f = p-rec p f I

rec₂ : (A : FinSet ℓ₁) (B : FinSet ℓ₂) {P : Type ℓ₃} → isProp P →
       (Iso ⟦ A ⟧ (Fin (card A)) → Iso ⟦ B ⟧ (Fin (card B)) → P) → P
rec₂ A B p f = rec A p λ a → rec B p (f a)

isFinite-n : ∀ {ℓ} n → isFinite (Lift {j = ℓ} (Fin n))
isFinite-n n = n , ∣ invIso LiftIso ∣

n-FinSet : ∀ {ℓ} n → FinSet ℓ
n-FinSet n = _ , isFinite-n n

⊤-FinSet : ∀ ℓ → FinSet ℓ
⊤-FinSet ℓ = n-FinSet 1

⊥-FinSet : ∀ ℓ → FinSet ℓ
⊥-FinSet ℓ = n-FinSet 0

LiftFinSet : ∀ {ℓ₁ ℓ₂} → FinSet ℓ₂ → FinSet (ℓ-max ℓ₁ ℓ₂)
LiftFinSet {ℓ₁} (A , m , p) =
  Lift {j = ℓ₁} A , m , p-rec propTruncIsProp (∣_∣ ∘ compIso (invIso LiftIso)) p
