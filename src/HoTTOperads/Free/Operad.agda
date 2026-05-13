{-# OPTIONS --cubical #-}
-- TODO(safe): discharge the postulated operadic structure on the fibres of CodeOp.
-- The construction follows graft + reinsertion of indices (FreeOperad.tex lines 244-277).
module HoTTOperads.Free.Operad where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Free.IR
open import HoTTOperads.Free.IR.Sethood using (Fiber)

private
  variable
    ℓc ℓe ℓk : Level

module _ {𝒰 : Universe ℓc ℓe} (K : Universe.Code 𝒰 → Type ℓk) where
  open Universe 𝒰

  -- The operations of the free operad: fibres of CodeOp K, parameterised by codes.
  FreeOps' : Code → Type _
  FreeOps' = Fiber {𝒰 = 𝒰} {K = K}

  -- The full operadic structure on the free operad. All five fields postulated for now.
  postulate
    FreeOperad : Operad 𝒰 FreeOps'
