{-# OPTIONS --cubical #-}
-- TODO(safe): discharge the universal property of the free operad (FreeOperad.tex 357-368).
module HoTTOperads.Free.Universal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Morphism
open import HoTTOperads.Free.IR
open import HoTTOperads.Free.IR.Sethood using (Fiber)
open import HoTTOperads.Free.Operad using (FreeOps' ; FreeOperad)

private
  variable
    ℓc ℓe ℓk ℓl : Level

module _ {𝒰 : Universe ℓc ℓe} (K : Universe.Code 𝒰 → Type ℓk) where
  open Universe 𝒰

  -- The unit of the free adjunction.
  postulate
    η : (A : Code) → K A → FreeOps' {𝒰 = 𝒰} K A

  -- Interpretation: given a target operad and a morphism of species, lift to operad map.
  postulate
    interpret : {L : Code → Type ℓl} (O : Operad 𝒰 L)
              → ((A : Code) → K A → L A)
              → FreeOperad K ⇒ O

  -- Universal property: the lifted morphism is unique up to a path.
  postulate
    universal : {L : Code → Type ℓl} (O : Operad 𝒰 L)
              → (f : (A : Code) → K A → L A)
              → isContr (Σ[ g ∈ (FreeOperad K ⇒ O) ]
                          ((A : Code) (k : K A) →
                             _⇒_.⟪_⟫ {𝒰 = 𝒰} g A (η A k) ≡ f A k))
