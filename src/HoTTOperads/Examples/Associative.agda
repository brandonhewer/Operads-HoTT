{-# OPTIONS --cubical #-}
-- The Associative operad: operations are the unit type at every index. Uniform over
-- any generalised operad universe.
module HoTTOperads.Examples.Associative where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Unit using (Unit ; tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe : Level

module _ (𝒰 : Universe ℓc ℓe) where
  open Universe 𝒰

  AssocOps : Code → Type
  AssocOps _ = Unit

  Associative : Operad 𝒰 AssocOps
  Operad.isSetK Associative _ = isSetUnit
    where open import Cubical.Data.Unit using (isSetUnit)
  Operad.id     Associative   = tt
  Operad.compₒ  Associative _ _ _ _ = tt
  Operad.idl    Associative _ _ i = tt
  Operad.idr    Associative _ _ i = tt
  Operad.assoc  Associative _ _ _ _ _ _ i = tt
