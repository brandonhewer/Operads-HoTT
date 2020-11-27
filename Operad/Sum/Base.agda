{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Sum.Base where

open import Cubical.Data.Sum

open import Cubical.Foundations.Prelude

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level
    A : Type ℓ₁
    B : Type ℓ₂
    C : Type ℓ₃

[_,_] : (A → C) → (B → C) -> A ⊎ B → C
[_,_] = elim

left : (A → C) → A ⊎ B → C ⊎ B
left f (inl x) = inl (f x)
left f (inr x) = inr x
