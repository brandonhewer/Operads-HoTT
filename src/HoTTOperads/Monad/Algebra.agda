{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Monad.Algebra
--
-- Algebras for a 𝒰-operad and their evaluation on `OpM` carriers.
--
-- Formalises from the paper:
--   Definition 8.3 (Section 8, Monad over an Operad) — `Algebra O X` and
--   the evaluation function `runAlg`.
-- ============================================================================
module HoTTOperads.Monad.Algebra where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Morphism
open import HoTTOperads.Operad.Endo
open import HoTTOperads.Monad.Base

private
  variable
    ℓc ℓe ℓk ℓ : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} where
  -- Definition 8.3 (Section 8, Monad over an Operad).
  -- An algebra over O is a carrier h-set X together with an operad morphism
  -- `O ⇒ Endo 𝒰 X`.
  Algebra : (O : Operad 𝒰 K) (X : Type ℓ) (isSetX : isSet X) → Type (ℓ-max (ℓ-max ℓc ℓe) (ℓ-max ℓk ℓ))
  Algebra O X isSetX = O ⇒ Endo 𝒰 isSetX

  -- Definition 8.3 (evaluation). Run an algebra: turn an OpM into a value in
  -- the carrier.
  runAlg : (O : Operad 𝒰 K) (X : Type ℓ) (isSetX : isSet X)
         → Algebra O X isSetX → OpM O X → X
  runAlg O X isSetX α (i ▷ k ▷ d) = _⇒_.⟪_⟫ α i k d
