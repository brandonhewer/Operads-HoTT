{-# OPTIONS --cubical #-}
module HoTTOperads.Operad.Specialised.NonSymm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Fin using (Fin)

open import HoTTOperads.Operad.Base
open import HoTTOperads.Universe.Instances.Nat using (𝓝)

private
  variable
    ℓ : Level

-- A planar (non-symmetric) operad on a family of h-sets K : ℕ → Type.
-- This is the paper's NonSymmOperad K (Section 4), recovered as Operad 𝓝 K.
NonSymmOperad : (K : ℕ → Type ℓ) → Type ℓ
NonSymmOperad K = Operad 𝓝 K
