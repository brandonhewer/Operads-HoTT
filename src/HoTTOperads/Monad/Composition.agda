{-# OPTIONS --cubical #-}
module HoTTOperads.Monad.Composition where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Functor

private
  variable
    ℓc ℓe ℓk ℓx ℓy : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} (O : Operad 𝒰 K) where
  open Universe 𝒰
  open Operad O

  -- Unit: store an element at the output of the unit operation.
  return : {X : Type ℓx} → X → OpM O X
  return x = 𝜏 ▷ id ▷ (λ _ → x)

  -- Dependent monadic composition: take an OpM, plus a continuation that uses the
  -- index, and produce a new OpM with the indices/operations composed.
  compM : {X : Type ℓx} {Y : Type ℓy}
        → (ox : OpM O X)
        → (El (Index ox) → X → OpM O Y)
        → OpM O Y
  compM (i ▷ k ▷ d) f =
    let next : (a : El i) → OpM O _
        next a = f a (d a)
    in  ⅀ i (λ a → Index (next a))
      ▷ compₒ i (λ a → Index (next a)) k (λ a → Op (next a))
      ▷ (λ ab → let (a , b) = equivFun (⟦⅀⟧ i (λ a → Index (next a))) ab
                in  Data (next a) b)

  -- Join: ordinary monadic multiplication.
  join : {X : Type ℓx} → OpM O (OpM O X) → OpM O X
  join o = compM o (λ _ x → x)
