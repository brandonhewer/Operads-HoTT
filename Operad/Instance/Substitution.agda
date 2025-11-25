{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Instance.Substitution where

open import Cubical.Data.FinData

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Operad.Base
open import Operad.FinSet.Small
open import Operad.Sigma hiding (comp)

record Monoid {ℓ₁ : Level} (X : Type ℓ₁) : Type ℓ₁ where
  field
    ε : X
    _+_ : X → X → X
    leftId : ∀ a → ε + a ≡ a
    rightId : ∀ a → a + ε ≡ a
    assoc : ∀ a b c → (a + b) + c ≡ a + (b + c)

open Monoid

_⟨_∙_⟩ : {ℓ₁ : Level} {X : Type ℓ₁} → Monoid X → X → X → X
M ⟨ x ∙ y ⟩ = _+_ M x y 

private
  variable
    ℓ₁ ℓ₂ : Level

open Operad

SubstOperad : {ℓ₁ : Level} {X : Type ℓ₂} →
              isSet X → Monoid X → Operad ℓ₁ (ℓ-max ℓ₁ ℓ₂)
Ops (SubstOperad {X = X} isSetX M) A = El A → X
isSetOps (SubstOperad isSetX M) _ = isSetΠ λ _ → isSetX
id (SubstOperad isSetX M) _ = ε M
comp (SubstOperad isSetX M) _ _ f g (a , b) = M ⟨ f a ∙ g a b ⟩
idl (SubstOperad {X = X} isSetX M) A f =
  ua→ λ { (lift zero , a) → leftId M (f (lift zero) a) }
idr (SubstOperad isSetX M) A f =
  ua→ λ { (a , lift zero) → rightId M (f a) }
assoc (SubstOperad isSetX M) A B C f fs fss =
  ua→ λ { ((a , b) , c) → assoc M (f a) (fs a b) (fss a b c) }
