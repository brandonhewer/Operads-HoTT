{-# OPTIONS --without-K #-}

open import Level
-- open import Relation.Binary.PropositionalEquality

private
  variable
    ℓ₁ : Level

data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  refl : x ≡ x

uip : {A : Set ℓ₁} {x y : A} (p q : x ≡ y) → p ≡ q
uip refl q = {!!}

trans′ : {A : Set ℓ₁} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans′ p q = {!!}

test : {A : Set ℓ₁} (f : A → A) →
       ∀ a → f a ≡ a → f (f a) ≡ a
test f a p = {!!}
