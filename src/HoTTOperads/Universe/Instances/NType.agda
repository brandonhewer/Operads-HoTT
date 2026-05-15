{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Universe.Instances.NType
--
-- For every homotopy level `n`, the universe `𝓗 n : Universe (ℓ-suc ℓ) ℓ`
-- of n-types: codes are `TypeOfHLevel ℓ n`, the interpretation is the
-- carrier projection, `⅀` is the dependent sum (n-types are closed under Σ),
-- the unit is `Unit*`, and `Inj` is the `Σ≡Prop`-of-`ua` equality (the
-- "is an n-type" proof is propositional). This is the n-type analogue of
-- the finite-set universe `𝓕`; the coherence laws collapse exactly as there.
--
-- Formalises from the paper:
--   Section 6 (Generalised Operad Universes) states that, for any homotopy
--   level n ≥ -1, the universe of n-types satisfies all the criteria of
--   Definition 6.3. This module is the concrete instance witnessing that
--   claim (uniform in `n`).
-- ============================================================================
module HoTTOperads.Universe.Instances.NType where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv ; compEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaCompEquiv)
open import Cubical.Foundations.HLevels
  using (HLevel ; TypeOfHLevel ; isPropIsOfHLevel ; isOfHLevelΣ ; isContr→isOfHLevel)
open import Cubical.Foundations.Structure using (⟨_⟩ ; str)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; Σ≡Prop)
open import Cubical.Data.Unit using (Unit ; Unit* ; isContrUnit* ; isContr→≃Unit)

open import HoTTOperads.Prelude.FinSet using (cong-fst-Σ≡Prop ; Σ≡Prop-∙)
open import HoTTOperads.Universe.Base

module _ {ℓ : Level} (n : HLevel) where

  -- Underlying type of an n-type code.
  El-N : TypeOfHLevel ℓ n → Type ℓ
  El-N A = ⟨ A ⟩

  -- Dependent sum of n-types: n-types are closed under Σ.
  ⅀N : (A : TypeOfHLevel ℓ n) → (El-N A → TypeOfHLevel ℓ n) → TypeOfHLevel ℓ n
  ⅀N A B = (Σ[ a ∈ El-N A ] El-N (B a)) , isOfHLevelΣ n (str A) (λ a → str (B a))

  -- The unit n-type: `Unit*`, contractible hence of every level.
  𝜏N : TypeOfHLevel ℓ n
  𝜏N = Unit* , isContr→isOfHLevel n isContrUnit*

  -- The closure equivalence is the identity; the underlying type is the Σ.
  ⟦⅀⟧N : (A : TypeOfHLevel ℓ n) (B : El-N A → TypeOfHLevel ℓ n)
        → El-N (⅀N A B) ≃ (Σ[ a ∈ El-N A ] El-N (B a))
  ⟦⅀⟧N _ _ = idEquiv _

  ⟦𝜏⟧N : El-N 𝜏N ≃ Unit
  ⟦𝜏⟧N = isContr→≃Unit isContrUnit*

  -- `Inj`: from an equivalence of carriers, an equality of n-types, via
  -- `Σ≡Prop` (the n-type proof is propositional) composed with `ua`.
  InjN : {A B : TypeOfHLevel ℓ n} → El-N A ≃ El-N B → A ≡ B
  InjN e = Σ≡Prop (λ _ → isPropIsOfHLevel n) (ua e)

  -- `Inj` distributes over equivalence composition: `uaCompEquiv` lifted
  -- through `Σ≡Prop`, exactly as for the finite-set universe.
  InjCompN : {A B C : TypeOfHLevel ℓ n}
             (e₁ : El-N A ≃ El-N B) (e₂ : El-N B ≃ El-N C)
           → InjN (compEquiv e₁ e₂) ≡ InjN e₁ ∙ InjN e₂
  InjCompN {A = A} {B = B} {C = C} e₁ e₂ =
      cong (Σ≡Prop (λ _ → isPropIsOfHLevel n) {u = A} {v = C}) (uaCompEquiv e₁ e₂)
    ∙ Σ≡Prop-∙ (λ _ → isPropIsOfHLevel n) {u = A} {v = B} {w = C} (ua e₁) (ua e₂)

  NTypeBase : UniverseBase (ℓ-suc ℓ) ℓ
  UniverseBase.Code    NTypeBase = TypeOfHLevel ℓ n
  UniverseBase.El      NTypeBase = El-N
  UniverseBase.⅀       NTypeBase = ⅀N
  UniverseBase.𝜏       NTypeBase = 𝜏N
  UniverseBase.⟦⅀⟧     NTypeBase = ⟦⅀⟧N
  UniverseBase.⟦𝜏⟧     NTypeBase = ⟦𝜏⟧N
  UniverseBase.Inj     NTypeBase = InjN
  UniverseBase.InjComp NTypeBase = InjCompN

  -- Each coherence reads `ua X ≡ cong El (Inj X)`. With `Inj = Σ≡Prop pp ∘ ua`
  -- and `El = ⟨_⟩`, the RHS is `cong fst (Σ≡Prop pp (ua X))`, which collapses
  -- to `ua X` by `cong-fst-Σ≡Prop`.
  NType-coh : UniverseCoh NTypeBase
  UniverseCoh.⟦⅀Idl⟧   NType-coh A =
    sym (cong-fst-Σ≡Prop (λ _ → isPropIsOfHLevel n)
                         {u = ⅀N 𝜏N (λ _ → A)} {v = A}
                         (ua (UniverseBase.⅀Idl≃ NTypeBase A)))
  UniverseCoh.⟦⅀Idr⟧   NType-coh A =
    sym (cong-fst-Σ≡Prop (λ _ → isPropIsOfHLevel n)
                         {u = ⅀N A (λ _ → 𝜏N)} {v = A}
                         (ua (UniverseBase.⅀Idr≃ NTypeBase A)))
  UniverseCoh.⟦⅀Assoc⟧ NType-coh A B C =
    sym (cong-fst-Σ≡Prop (λ _ → isPropIsOfHLevel n)
                         {u = ⅀N A (λ a → ⅀N (B a) (C a))}
                         {v = ⅀N (⅀N A B) (UniverseBase.⅀Assoc-C' NTypeBase A B C)}
                         (ua (UniverseBase.⅀Assoc≃ NTypeBase A B C)))

  -- Definition 6.3 instance (Section 6, Generalised Operad Universes).
  -- The universe of n-types at homotopy level `n`.
  𝓗 : Universe (ℓ-suc ℓ) ℓ
  Universe.base 𝓗 = NTypeBase
  Universe.coh  𝓗 = NType-coh
