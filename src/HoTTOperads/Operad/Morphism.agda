{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Operad.Morphism
--
-- Morphisms of 𝒰-operads: a family of functions on operations together with
-- proofs that the unit and composition operations are preserved. Together
-- with `id⇒` and `_●_` this gives the data of the category of 𝒰-operads.
--
-- Formalises from the paper:
--   Definition 7.1  (Section 7, Category of Operads) — `_⇒_`, `id⇒`, `_●_`.
--   Proposition 7.2 (Section 7, Category of Operads) — `morphism-≡` and the
--                   equivalence `morphism-≡-equiv`.
-- ============================================================================
module HoTTOperads.Operad.Morphism where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Path using (isProp→SquareP)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe ℓk ℓl : Level

-- Definition 7.1 (Section 7, Category of Operads).
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

-- Identity morphism (identity arrow of Definition 7.1).
id⇒ : ∀ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} (O : Operad 𝒰 K) → O ⇒ O
_⇒_.⟪_⟫    (id⇒ O) _ k         = k
_⇒_.on-id  (id⇒ O)             = refl
_⇒_.on-comp (id⇒ O) _ _ _ _    = refl

-- Composition of operad morphisms (composition arrow of Definition 7.1).
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

-- ============================================================================
-- Proposition 7.2 (Section 7, Category of Operads).
--
-- Equality of operad morphisms is determined by their underlying maps.
-- `morphism-≡` provides Σ-extensionality from pointwise agreement;
-- `morphism-≡-equiv` upgrades this to the equivalence
--   (f ≡ g) ≃ (⟪ f ⟫ ≡ ⟪ g ⟫).
-- The on-id / on-comp fields are paths in the h-set `L _` (the `isSetK`
-- field of `Oᴸ`), hence propositional and recovered by `isProp→PathP`.
-- ============================================================================
module _ {𝒰 : Universe ℓc ℓe}
         {K : Universe.Code 𝒰 → Type ℓk} {L : Universe.Code 𝒰 → Type ℓl}
         {Oᴷ : Operad 𝒰 K} {Oᴸ : Operad 𝒰 L} where
  open Universe 𝒰
  open Operad

  -- Σ-extensionality: pointwise-equal underlying maps yield equal morphisms.
  morphism-≡ : (f g : Oᴷ ⇒ Oᴸ)
             → ((A : Code) (k : K A) → _⇒_.⟪_⟫ f A k ≡ _⇒_.⟪_⟫ g A k)
             → f ≡ g
  _⇒_.⟪_⟫    (morphism-≡ f g eq i) A k = eq A k i
  _⇒_.on-id  (morphism-≡ f g eq i) =
    isProp→PathP (λ i' → isSetK Oᴸ 𝜏 (eq 𝜏 (id Oᴷ) i') (id Oᴸ))
                  (_⇒_.on-id f) (_⇒_.on-id g) i
  _⇒_.on-comp (morphism-≡ f g eq i) A B k ks =
    isProp→PathP (λ i' → isSetK Oᴸ (⅀ A B) (eq (⅀ A B) (compₒ Oᴷ A B k ks) i')
                                            (compₒ Oᴸ A B (eq A k i')
                                                          (λ a → eq (B a) (ks a) i')))
                  (_⇒_.on-comp f A B k ks)
                  (_⇒_.on-comp g A B k ks) i

  -- Retraction filler, defined by copatterns. At the i=i0 boundary it
  -- reduces to `morphism-≡ f g (cong ⟪_⟫ p)`; at i=i1 it reduces to `p`.
  private
    ret-≡ : (f g : Oᴷ ⇒ Oᴸ) (p : f ≡ g)
          → morphism-≡ f g (λ A k → λ i → _⇒_.⟪_⟫ (p i) A k) ≡ p
    _⇒_.⟪_⟫    (ret-≡ f g p i j) A k = _⇒_.⟪_⟫ (p j) A k
    _⇒_.on-id  (ret-≡ f g p i j) =
      isProp→SquareP
        (λ _ j' → isSetK Oᴸ 𝜏 (_⇒_.⟪_⟫ (p j') 𝜏 (id Oᴷ)) (id Oᴸ))
        refl refl
        (λ j' → _⇒_.on-id (morphism-≡ f g (λ A k → λ i' → _⇒_.⟪_⟫ (p i') A k) j'))
        (λ j' → _⇒_.on-id (p j'))
        i j
    _⇒_.on-comp (ret-≡ f g p i j) A B k ks =
      isProp→SquareP
        (λ _ j' → isSetK Oᴸ (⅀ A B)
                    (_⇒_.⟪_⟫ (p j') (⅀ A B) (compₒ Oᴷ A B k ks))
                    (compₒ Oᴸ A B (_⇒_.⟪_⟫ (p j') A k)
                                  (λ a → _⇒_.⟪_⟫ (p j') (B a) (ks a))))
        refl refl
        (λ j' → _⇒_.on-comp (morphism-≡ f g (λ A' k' → λ i' → _⇒_.⟪_⟫ (p i') A' k') j') A B k ks)
        (λ j' → _⇒_.on-comp (p j') A B k ks)
        i j

  -- Proposition 7.2 (the equivalence). cong ⟪_⟫ is an equivalence onto
  -- pointwise equalities.
  morphism-≡-equiv : (f g : Oᴷ ⇒ Oᴸ)
                   → (f ≡ g)
                   ≃ ((A : Code) (k : K A) → _⇒_.⟪_⟫ f A k ≡ _⇒_.⟪_⟫ g A k)
  morphism-≡-equiv f g = isoToEquiv ext-iso
    where
      ext-iso : Iso (f ≡ g) ((A : Code) (k : K A) → _⇒_.⟪_⟫ f A k ≡ _⇒_.⟪_⟫ g A k)
      Iso.fun     ext-iso p A k = λ i → _⇒_.⟪_⟫ (p i) A k
      Iso.inv     ext-iso eq    = morphism-≡ f g eq
      Iso.rightInv ext-iso eq   = refl
      Iso.leftInv  ext-iso p    = ret-≡ f g p
