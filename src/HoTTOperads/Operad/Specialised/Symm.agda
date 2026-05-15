{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Operad.Specialised.Symm
--
-- Symmetric operads as a specialisation of the generalised `Operad` record
-- at the universe `𝓕` (Bishop-finite sets).
--
-- Formalises from the paper:
--   Definition 5.2 (Section 5, Symmetric Operads) — `SymmOperad K`.
-- The symmetric group action is induced by path substitution over A ≡ A
-- in FinSet (the right action of A's automorphisms).
-- ============================================================================
module HoTTOperads.Operad.Specialised.Symm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.FinSet.Base using (FinSet)

open import HoTTOperads.Operad.Base
open import HoTTOperads.Universe.Instances.FinSet using (𝓕)

private
  variable
    ℓ : Level

-- Definition 5.2 (Section 5, Symmetric Operads).
-- A symmetric operad on a family of h-sets K : FinSet → Type, realised as a
-- `𝓕`-operad.
SymmOperad : (K : FinSet ℓ-zero → Type ℓ) → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
SymmOperad K = Operad 𝓕 K
