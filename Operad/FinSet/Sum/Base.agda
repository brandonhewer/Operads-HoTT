{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Sum.Base where

open import Cubical.Data.Nat

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.Sum

private
  variable
    ℓ₁ ℓ₂ : Level

isFinite⊎ : {A : Type ℓ₁} {B : Type ℓ₂} → isFinite A → isFinite B → isFinite (A ⊎ B)
isFinite⊎ (m , I′₁) (n , I′₂) =
  m + n ,
  p-rec squash (λ I₁ →
    p-rec squash (λ I₂ →
      ∣ compIso (⊎Iso I₁ I₂) (Fin⊎↔Fin+ m n) ∣
    ) I′₂
  ) I′₁

_∣⊎∣_ : ∀ {ℓ₁ ℓ₂} → FinSet ℓ₁ → FinSet ℓ₂ → FinSet (ℓ-max ℓ₁ ℓ₂)
(X , I₁) ∣⊎∣ (Y , I₂) = X ⊎ Y , isFinite⊎ I₁ I₂
