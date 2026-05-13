{-# OPTIONS --cubical #-}
module HoTTOperads.Operad.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe ℓk ℓl : Level

-- An operad morphism: a family of maps on operations respecting unit and composition.
record _⇒_ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} {L : Universe.Code 𝒰 → Type ℓl}
           (Oᴷ : Operad 𝒰 K) (Oᴸ : Operad 𝒰 L) : Type (ℓ-max (ℓ-max ℓc ℓe) (ℓ-max ℓk ℓl)) where
  open Universe 𝒰
  open Operad

  field
    ⟪_⟫    : (A : Code) → K A → L A
    on-id  : ⟪_⟫ 𝜏 (id Oᴷ) ≡ id Oᴸ
    on-comp : (A : Code) (B : El A → Code)
              (k : K A) (ks : (a : El A) → K (B a))
            → ⟪_⟫ (⅀ A B) (compₒ Oᴷ A B k ks)
            ≡ compₒ Oᴸ A B (⟪_⟫ A k) (λ a → ⟪_⟫ (B a) (ks a))

-- Identity morphism.
id⇒ : ∀ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} (O : Operad 𝒰 K) → O ⇒ O
_⇒_.⟪_⟫    (id⇒ O) _ k         = k
_⇒_.on-id  (id⇒ O)             = refl
_⇒_.on-comp (id⇒ O) _ _ _ _    = refl

-- Composition of operad morphisms.
_●_ : ∀ {𝒰 : Universe ℓc ℓe}
        {K : Universe.Code 𝒰 → Type ℓk} {L : Universe.Code 𝒰 → Type ℓl}
        {M : Universe.Code 𝒰 → Type ℓl}
        {Oᴷ : Operad 𝒰 K} {Oᴸ : Operad 𝒰 L} {Oᴹ : Operad 𝒰 M}
      → Oᴸ ⇒ Oᴹ → Oᴷ ⇒ Oᴸ → Oᴷ ⇒ Oᴹ
_⇒_.⟪_⟫     (g ● f) A k = _⇒_.⟪_⟫ g A (_⇒_.⟪_⟫ f A k)
_⇒_.on-id   (g ● f)     = cong (_⇒_.⟪_⟫ g _) (_⇒_.on-id f) ∙ _⇒_.on-id g
_⇒_.on-comp (_●_ {𝒰 = 𝒰} g f) A B k ks =
    cong (_⇒_.⟪_⟫ g (Universe.⅀ 𝒰 A B)) (_⇒_.on-comp f A B k ks)
  ∙ _⇒_.on-comp g A B (_⇒_.⟪_⟫ f A k) (λ a → _⇒_.⟪_⟫ f (B a) (ks a))
