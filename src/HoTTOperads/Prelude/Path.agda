{-# OPTIONS --cubical #-}
module HoTTOperads.Prelude.Path where

open import Cubical.Foundations.Prelude public
open import Cubical.Foundations.Path public
open import Cubical.Foundations.Transport public
open import Cubical.Foundations.GroupoidLaws public

private
  variable
    ℓ ℓ' : Level

-- Swap the index path of a PathP by an equality between two ≡-paths in a set.
-- Standard idiom for closing operadic-law proofs: build a PathP along a
-- *convenient* index path, then re-target it onto the *required* index path
-- (typically Universe.Inj …) via an isSet substitution.
opaque
  isSet→subst-PathP : {A : Type ℓ} (isSetA : isSet A)
                      {B : A → Type ℓ'} {x y : A}
                      (p q : x ≡ y) {a : B x} {b : B y}
                    → PathP (λ i → B (p i)) a b
                    → PathP (λ i → B (q i)) a b
  isSet→subst-PathP isSetA {B = B} {x = x} {y = y} p q {a = a} {b = b} pp =
    subst (λ r → PathP (λ i → B (r i)) a b) (isSetA x y p q) pp
