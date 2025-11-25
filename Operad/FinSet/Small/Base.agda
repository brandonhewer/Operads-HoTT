{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Small.Base where

open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Univalence

open import Cubical.Relation.Nullary

open import Operad.Fin
open import Operad.Sigma

private
  variable
    ℓ₁ ℓ₂ : Level
    U : Type ℓ₁

data FinClosure {U : Type ℓ₁} (P : U → Type ℓ₂) : Type (ℓ-max ℓ₁ (ℓ-suc ℓ₂))

El : {P : U → Type ℓ₂} → FinClosure P → Type ℓ₂

data FinClosure {U = U} P where
  Ty : (u : U) → FinClosure P
  ⊥F : FinClosure P
  ⊤F : FinClosure P
  ΣF : (A : FinClosure P) → (El A → FinClosure P) → FinClosure P
  ΠF : (A : FinClosure P) → (El A → FinClosure P) → FinClosure P
  ≡F : (A : FinClosure P) → El A → El A → FinClosure P
  ¬F : (A : FinClosure P) → FinClosure P
  un : ∀ x y → El x ≃ El y → x ≡ y

El {P = P} (Ty u) = P u
El ⊥F             = Lift (Fin 0)
El ⊤F             = Lift ⊤
El (ΣF A B)       = Σ (El A) (El ∘ B)
El (ΠF A B)       = (a : El A) → El (B a)
El (≡F A a b)     = a ≡ b
El (¬F A)         = ¬ (El A)
El (un A₁ A₂ p i) = ua p i
