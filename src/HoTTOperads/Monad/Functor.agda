{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Monad.Functor
--
-- The functorial action `_<$>_` on `OpM O` and the two functor laws.
--
-- Formalises from the paper:
--   Theorem 8.2 (Section 8, Monad over an Operad) — functor part of
--   `OpM O` being a monad.
-- ============================================================================
module HoTTOperads.Monad.Functor where

open import Cubical.Foundations.Prelude

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base

private
  variable
    ℓc ℓe ℓk ℓx ℓy : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} {O : Operad 𝒰 K} where
  -- Theorem 8.2 (functor map). Direct definition preserves the index (avoiding
  -- the more general compM form which would change it to ⅀ Index (λ _ → 𝜏)).
  _<$>_ : {X : Type ℓx} {Y : Type ℓy} → (X → Y) → OpM O X → OpM O Y
  f <$> (i ▷ k ▷ d) = i ▷ k ▷ (λ x → f (d x))

  opaque
    -- Theorem 8.2 (functor laws). Hold definitionally for this representation.
    <$>-id : {X : Type ℓx} (o : OpM O X) → (λ x → x) <$> o ≡ o
    <$>-id _ = refl

    <$>-∘ : {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓy}
          → (f : Y → Z) (g : X → Y) (o : OpM O X)
          → (λ x → f (g x)) <$> o ≡ (f <$> (g <$> o))
    <$>-∘ _ _ _ = refl
