{-# OPTIONS --cubical #-}
module HoTTOperads.Operad.Specialised.Symm where

open import Cubical.Foundations.Prelude
open import Cubical.Data.FinSet.Base using (FinSet)

open import HoTTOperads.Operad.Base
open import HoTTOperads.Universe.Instances.FinSet using (𝓕)

private
  variable
    ℓ : Level

-- A symmetric operad on a family of h-sets K : FinSet → Type.
-- Recovered as Operad 𝓕 K; the symmetric group action is induced by path substitution
-- over A ≡ A in FinSet (the right action of A's automorphisms).
SymmOperad : (K : FinSet ℓ-zero → Type ℓ) → Type (ℓ-max (ℓ-suc ℓ-zero) ℓ)
SymmOperad K = Operad 𝓕 K
