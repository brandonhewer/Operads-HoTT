{-# OPTIONS --cubical #-}
-- The free planar operad on a family K : ℕ → Type. Recovered by specialising
-- the generalised free operad to 𝒰 = 𝓝.
module HoTTOperads.Free.Examples where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)

open import HoTTOperads.Universe.Instances.Nat using (𝓝)
open import HoTTOperads.Free.IR using (FreeOpsIR ; leaf ; node ; CodeOp)
open import HoTTOperads.Free.Operad using (FreeOps')

private
  variable
    ℓ : Level

-- Free planar operad operations on K : ℕ → Type.
FreePLOps : (K : ℕ → Type ℓ) → ℕ → Type _
FreePLOps K = FreeOps' {𝒰 = 𝓝} K
