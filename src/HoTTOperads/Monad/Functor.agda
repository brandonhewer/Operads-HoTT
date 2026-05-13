{-# OPTIONS --cubical #-}
module HoTTOperads.Monad.Functor where

open import Cubical.Foundations.Prelude

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base

private
  variable
    ℓc ℓe ℓk ℓx ℓy : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} {O : Operad 𝒰 K} where
  -- Functorial map. Direct definition preserves the index (avoiding the more general
  -- compM form which would change it to ⅀ Index (λ _ → 𝜏)).
  _<$>_ : {X : Type ℓx} {Y : Type ℓy} → (X → Y) → OpM O X → OpM O Y
  f <$> (i ▷ k ▷ d) = i ▷ k ▷ (λ x → f (d x))

  opaque
    -- Functor laws hold definitionally.
    <$>-id : {X : Type ℓx} (o : OpM O X) → (λ x → x) <$> o ≡ o
    <$>-id _ = refl

    <$>-∘ : {X : Type ℓx} {Y : Type ℓy} {Z : Type ℓy}
          → (f : Y → Z) (g : X → Y) (o : OpM O X)
          → (λ x → f (g x)) <$> o ≡ (f <$> (g <$> o))
    <$>-∘ _ _ _ = refl
