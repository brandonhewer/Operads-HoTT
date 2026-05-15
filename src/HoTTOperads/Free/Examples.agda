{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Free.Examples
--
-- Free planar operad on a family K : ℕ → Type. Obtained by specialising the
-- generalised free operad of HoTTOperads.Free.IR to the universe 𝓝.
--
-- Formalises from the paper:
--   Definition 9.1 (Section 9, Free Operad) — `FreePLOps K`.
-- ============================================================================
module HoTTOperads.Free.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)

open import HoTTOperads.Universe.Instances.Nat using (𝓝)
open import HoTTOperads.Free.IR using (FreeOpsIR ; leaf ; node ; CodeOp ; FreeOps')

private
  variable
    ℓ : Level

-- Definition 9.1 (Section 9, Free Operad).
-- Free planar operad operations on K : ℕ → Type.
FreePLOps : (K : ℕ → Type ℓ) → ℕ → Type _
FreePLOps K = FreeOps' {𝒰 = 𝓝} K
