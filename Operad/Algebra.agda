{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Algebra where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude

open import Operad.Base
open import Operad.Instance.Endo
open import Operad.Morphism

private
  variable
    ℓ₁ ℓ₂ : Level

record Algebra (O : Operad ℓ₁ ℓ₂) : Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂)) where
  field
    Carrier : hSet ℓ₁
    run-alg : O ⇒ᵒᵖ Endo (snd Carrier)
