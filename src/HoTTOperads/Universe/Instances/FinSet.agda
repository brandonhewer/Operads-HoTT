{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Universe.Instances.FinSet
--
-- The symmetric operad universe `𝓕 : Universe ℓ-zero ℓ-zero` on Bishop-finite
-- sets: codes are `FinSet`, interpretation is the carrier projection, ⅀ is
-- the Σ-of-finite-sets, 𝜏 is `Unit`, and `Inj` is the Σ≡Prop-induced
-- equality on the (type, isFinSet) pair.
--
-- Formalises from the paper:
--   `𝓕 : Universe` is the concrete instance of Definition 6.1
--   (Section 6, GeneralisedUniverses) used in Section 5 (Symmetric Operads),
--   where `SymmOperad K = Operad 𝓕 K` matches Definition 5.2.
--   `FinSet` itself realises Definition 5.1.
-- ============================================================================
module HoTTOperads.Universe.Instances.FinSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.FinSet.Base using (FinSet ; isFinSet ; isPropIsFinSet)
open import Cubical.Data.FinSet.Constructors using (isFinSetΣ)
open import Cubical.Data.FinSet.Properties using (isFinSetUnit)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)

open import HoTTOperads.Prelude.FinSet using (cong-fst-Σ≡Prop ; Σ≡Prop-∙)
open import HoTTOperads.Universe.Base

private
  ℓ : Level
  ℓ = ℓ-zero

-- Underlying type of a finite set.
El-FS : FinSet ℓ → Type ℓ
El-FS A = A .fst

-- Local opaque wrapper around the *expensive* FinSet-stdlib witness for Σ.
-- The recursive card-arithmetic in `isFinSetΣ`'s first projection plus the
-- truncation in its second was the dominant cost when `⅀FS A B` reduced
-- across operadic proofs; sealing the entire pair prevents that expansion.
opaque
  isFinSetΣ-op : (A : FinSet ℓ) (B : El-FS A → FinSet ℓ)
               → isFinSet (Σ[ a ∈ El-FS A ] El-FS (B a))
  isFinSetΣ-op A B = isFinSetΣ A B

-- Dependent sum of finite sets: ⅀ A B carries the underlying Σ-type with its finite-set proof.
⅀FS : (A : FinSet ℓ) → (El-FS A → FinSet ℓ) → FinSet ℓ
⅀FS A B = (Σ[ a ∈ El-FS A ] El-FS (B a))
        , isFinSetΣ-op A (λ a → B a)

-- The unit finite set. isFinSetUnit is kept transparent because downstream
-- dot-patterns on `𝜏` (e.g. `sym-idr .𝜏 id↑`) need this to reduce.
𝜏FS : FinSet ℓ
𝜏FS = Unit , isFinSetUnit

-- The closure equivalence is the identity (the underlying Σ-type is exactly Σ A (El ∘ B)).
⟦⅀⟧FS : (A : FinSet ℓ) (B : El-FS A → FinSet ℓ)
      → El-FS (⅀FS A B) ≃ (Σ[ a ∈ El-FS A ] El-FS (B a))
⟦⅀⟧FS _ _ = idEquiv _

⟦𝜏⟧FS : El-FS 𝜏FS ≃ Unit
⟦𝜏⟧FS = idEquiv _

-- InjFS kept transparent: `Inj FinSetBase = InjFS'` and FinSet-coh's bodies
-- need InjFS to reduce to `Σ≡Prop pp ∘ ua` for the coherence types to match.
InjFS : (A B : FinSet ℓ) → El-FS A ≃ El-FS B → A ≡ B
InjFS _ _ e = Σ≡Prop (λ _ → isPropIsFinSet) (ua e)

opaque
  -- Inj distributes over equivalence composition: uaCompEquiv lifts through Σ≡Prop.
  InjCompFS : (A B C : FinSet ℓ)
              (e₁ : El-FS A ≃ El-FS B) (e₂ : El-FS B ≃ El-FS C)
            → InjFS A C (compEquiv e₁ e₂) ≡ InjFS A B e₁ ∙ InjFS B C e₂
  InjCompFS A B C e₁ e₂ =
      cong (Σ≡Prop (λ _ → isPropIsFinSet) {u = A} {v = C}) (uaCompEquiv e₁ e₂)
    ∙ Σ≡Prop-∙ (λ _ → isPropIsFinSet) {u = A} {v = B} {w = C} (ua e₁) (ua e₂)

-- Implicit-arg wrappers for use as record fields.
InjFS' : {A B : FinSet ℓ} → El-FS A ≃ El-FS B → A ≡ B
InjFS' {A} {B} = InjFS A B

InjCompFS' : {A B C : FinSet ℓ}
             (e₁ : El-FS A ≃ El-FS B) (e₂ : El-FS B ≃ El-FS C)
           → InjFS' (compEquiv e₁ e₂) ≡ InjFS' e₁ ∙ InjFS' e₂
InjCompFS' {A} {B} {C} = InjCompFS A B C

FinSetBase : UniverseBase (ℓ-suc ℓ) ℓ
UniverseBase.Code     FinSetBase = FinSet ℓ
UniverseBase.El       FinSetBase = El-FS
UniverseBase.⅀        FinSetBase = ⅀FS
UniverseBase.𝜏        FinSetBase = 𝜏FS
UniverseBase.⟦⅀⟧      FinSetBase = ⟦⅀⟧FS
UniverseBase.⟦𝜏⟧      FinSetBase = ⟦𝜏⟧FS
UniverseBase.Inj      FinSetBase = InjFS'
UniverseBase.InjComp  FinSetBase = InjCompFS'

-- Coherence laws: each says ua X ≡ cong El (Inj X). With Inj = Σ≡Prop pp ∘ ua and
-- El = fst, the RHS is cong fst (Σ≡Prop pp (ua X)), which collapses to ua X.
FinSet-coh : UniverseCoh FinSetBase
UniverseCoh.⟦⅀Idl⟧   FinSet-coh A =
  sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                       {u = ⅀FS 𝜏FS (λ _ → A)} {v = A}
                       (ua (UniverseBase.⅀Idl≃ FinSetBase A)))
UniverseCoh.⟦⅀Idr⟧   FinSet-coh A =
  sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                       {u = ⅀FS A (λ _ → 𝜏FS)} {v = A}
                       (ua (UniverseBase.⅀Idr≃ FinSetBase A)))
UniverseCoh.⟦⅀Assoc⟧ FinSet-coh A B C =
  sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                       {u = ⅀FS A (λ a → ⅀FS (B a) (C a))}
                       {v = ⅀FS (⅀FS A B) (UniverseBase.⅀Assoc-C' FinSetBase A B C)}
                       (ua (UniverseBase.⅀Assoc≃ FinSetBase A B C)))

-- Definition 6.1 instance (Section 6, GeneralisedUniverses).
-- The symmetric operad universe on Bishop-finite sets (Definition 5.1).
𝓕 : Universe (ℓ-suc ℓ) ℓ
Universe.base 𝓕 = FinSetBase
Universe.coh  𝓕 = FinSet-coh
