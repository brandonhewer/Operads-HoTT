{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Universe.Instances.Type
--
-- The universe `𝓣 : Universe (ℓ-suc ℓ) ℓ` whose codes are types themselves:
-- `Code = Type ℓ`, the interpretation is the identity, `⅀` is the dependent
-- sum `Σ`, the unit code is `Unit*`, the representation map `Inj` is `ua`
-- (univalence), and `InjComp` is `uaCompEquiv`. This is the univalent
-- universe; the three closure laws hold definitionally since the
-- interpretation is the identity (`cong El p` is `p`).
--
-- Formalises from the paper:
--   Section 6 (Generalised Operad Universes) states that the universe
--   `Type` itself satisfies all the criteria of Definition 6.3. This module
--   is the concrete instance witnessing that claim.
-- ============================================================================
module HoTTOperads.Universe.Instances.Type where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (idEquiv ; compEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaCompEquiv)
open import Cubical.Data.Sigma using (Σ ; _,_)
open import Cubical.Data.Unit using (Unit ; Unit* ; isContrUnit* ; isContr→≃Unit)

open import HoTTOperads.Universe.Base

private
  variable
    ℓ : Level

-- Codes are types; interpretation is the identity; the dependent-sum former
-- is `Σ`; the unit is `Unit*`; the interpretation equivalences are the
-- identity; `Inj` is `ua` and its composition coherence is `uaCompEquiv`.
TypeBase : UniverseBase (ℓ-suc ℓ) ℓ
UniverseBase.Code    (TypeBase {ℓ}) = Type ℓ
UniverseBase.El      TypeBase A     = A
UniverseBase.⅀       TypeBase A B   = Σ A B
UniverseBase.𝜏       TypeBase       = Unit*
UniverseBase.⟦⅀⟧     TypeBase A B   = idEquiv _
UniverseBase.⟦𝜏⟧     TypeBase       = isContr→≃Unit isContrUnit*
UniverseBase.Inj     TypeBase       = ua
UniverseBase.InjComp TypeBase       = uaCompEquiv

-- Each closure law reads `ua X ≡ cong El (Inj X)`. With `Inj = ua` and
-- `El` the identity, `cong El (ua X)` is `ua X`, so every law is `refl`.
TypeCoh : UniverseCoh (TypeBase {ℓ})
UniverseCoh.⟦⅀Idl⟧   TypeCoh A     = refl
UniverseCoh.⟦⅀Idr⟧   TypeCoh A     = refl
UniverseCoh.⟦⅀Assoc⟧ TypeCoh A B C = refl

-- Definition 6.3 instance (Section 6, Generalised Operad Universes).
-- The univalent universe of types.
𝓣 : Universe (ℓ-suc ℓ) ℓ
Universe.base 𝓣 = TypeBase
Universe.coh  𝓣 = TypeCoh
