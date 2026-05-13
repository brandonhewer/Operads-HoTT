{-# OPTIONS --cubical #-}
module HoTTOperads.Monad.Base where

open import Cubical.Foundations.Prelude

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe ℓk ℓx : Level

-- The monad over an operad. An OpM O X is an operation with data attached at each input.
-- Constructor: Index ▷ Op ▷ Data.
record OpM {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk}
           (O : Operad 𝒰 K) (X : Type ℓx)
         : Type (ℓ-max (ℓ-max ℓc ℓe) (ℓ-max ℓk ℓx)) where
  constructor _▷_▷_
  open Universe 𝒰
  field
    Index : Code
    Op    : K Index
    Data  : El Index → X

open OpM public
