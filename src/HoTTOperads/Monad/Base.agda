{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Monad.Base
--
-- The carrier type of the monad associated with a 𝒰-operad.
--
-- Formalises from the paper:
--   Definition 8.1 (Section 8, Monad over an Operad) — `OpM O X`.
-- ============================================================================
module HoTTOperads.Monad.Base where

open import Cubical.Foundations.Prelude

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe ℓk ℓx : Level

-- Definition 8.1 (Section 8, Monad over an Operad).
-- An `OpM O X` packages an arity code, an operation at that arity, and a
-- decoration assigning an `X` to each input slot.
record OpM {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk}
           (O : Operad 𝒰 K) (X : Type ℓx)
         : Type (ℓ-max (ℓ-max ℓc ℓe) (ℓ-max ℓk ℓx)) where
  constructor _▷_▷_
  open Universe 𝒰
  field
    Index : Code
    Op    : K Index
    Data  : El Index → X

open OpM public
