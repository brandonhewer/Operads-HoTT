{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Operad.Specialised.NonSymm
--
-- Planar (non-symmetric) operads as a specialisation of the generalised
-- `Operad` record at the universe `𝓝`.
--
-- Formalises from the paper:
--   Definition 4.1 (Section 4, Planar Operads) — `NonSymmOperad K`.
-- ============================================================================
module HoTTOperads.Operad.Specialised.NonSymm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Fin using (Fin)

open import HoTTOperads.Operad.Base
open import HoTTOperads.Universe.Instances.Nat using (𝓝)

private
  variable
    ℓ : Level

-- Definition 4.1 (Section 4, Planar Operads).
-- A planar (non-symmetric) operad on a family of h-sets K : ℕ → Type,
-- realised as a `𝓝`-operad.
NonSymmOperad : (K : ℕ → Type ℓ) → Type ℓ
NonSymmOperad K = Operad 𝓝 K
