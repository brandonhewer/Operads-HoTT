{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Examples.Commutative
--
-- The Commutative operad: operations are the unit type at every index.
-- Uniform over any generalised operad universe. (Identical structure to
-- Associative; the difference in semantics is intentional and degenerate at
-- this h-level.) Not numbered in the paper.
-- ============================================================================
module HoTTOperads.Examples.Commutative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (Unit ; tt ; isSetUnit)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe : Level

module _ (𝒰 : Universe ℓc ℓe) where
  open Universe 𝒰

  CommOps : Code → Type
  CommOps _ = Unit

  Commutative : Operad 𝒰 CommOps
  Operad.isSetK Commutative _ = isSetUnit
  Operad.id     Commutative   = tt
  Operad.compₒ  Commutative _ _ _ _ = tt
  Operad.idl    Commutative _ _ i = tt
  Operad.idr    Commutative _ _ i = tt
  Operad.assoc  Commutative _ _ _ _ _ _ i = tt
