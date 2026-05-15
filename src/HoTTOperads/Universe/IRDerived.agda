{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Universe.IRDerived
--
-- Derived universe paths: `⅀IdlD` is the left-identity rewrite
-- `X (invEq ⟦𝜏⟧ tt) ≡ ⅀ 𝜏 X`, and `⅀AssocD` the re-association of an
-- iterated `⅀`, both presented as the explicit `⅀Idl`/`⅀Assoc` composites.
--
-- Maintenance note: `Free.HIT`'s `graft` left/right-identity and
-- associativity proofs depend on the definitional shape of these two
-- definitions inside `subst (FreeOps K) …`; keep their bodies as the
-- explicit composites below rather than abstracting them.
--
-- No paper-numbered statements live here; the file provides infrastructure
-- used by Section 9 (Free Operad) for the leaf/node cases of `graft`.
-- ============================================================================
module HoTTOperads.Universe.IRDerived where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit ; tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived

private
  variable
    ℓc ℓe : Level

module _ {ℓc ℓe : Level} (𝒰 : Universe ℓc ℓe) where
  open Universe 𝒰

  -- `⅀IdlD` / `⅀AssocD`: the path-valued left-identity and associativity
  -- rewrites on `⅀` (see the module header for the `Free.HIT` dependency).
  ⅀IdlD : (X : El 𝜏 → Code) → X (invEq ⟦𝜏⟧ tt) ≡ ⅀ 𝜏 X
  ⅀IdlD X =
    sym (⅀Idl 𝒰 (X (invEq ⟦𝜏⟧ tt))) ∙ cong (⅀ 𝜏) const-X
    where
      const-X : (λ (_ : El 𝜏) → X (invEq ⟦𝜏⟧ tt)) ≡ X
      const-X = funExt (λ e → cong X (retEq ⟦𝜏⟧ e))

  ⅀AssocD : (A : Code) (B : El A → Code)
            (C : El (⅀ A B) → Code)
          → ⅀ A (λ a → ⅀ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b))))
          ≡ ⅀ (⅀ A B) C
  ⅀AssocD A B C =
    ⅀Assoc 𝒰 A B C' ∙ cong (⅀ (⅀ A B)) C'-eq
    where
      C' : (a : El A) → El (B a) → Code
      C' a b = C (invEq (⟦⅀⟧ A B) (a , b))

      C'-eq : ⅀Assoc-C' A B C' ≡ C
      C'-eq = funExt (λ x → cong C (retEq (⟦⅀⟧ A B) x))
