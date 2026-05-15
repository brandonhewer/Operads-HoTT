{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Operad.HLevel
--
-- The heterogeneous path space between two 𝒰-operads is propositional, and
-- the Σ-type of (h-set family, operad on it) is a 1-groupoid.
--
-- Formalises from the paper:
--   Proposition 6.5 (Section 6, Generalised Operad Universes) — `isPropOperadPathP`,
--                   `isSetOperad`, and `isGroupoid-Operad-Σ`.
--
-- Strategy. We unfold `Operad 𝒰 K` into a Σ-presentation `OperadΣ K`.
-- Each component of the Σ is either propositional (`isSetK`, `idl`, `idr`,
-- `assoc`) or an h-set value (`id`, `compₒ`), so `OperadΣ K` is an h-set
-- by `isOfHLevelΣ`. We then transport h-set-hood across the `Iso` between
-- `Operad 𝒰 K` and `OperadΣ K`. The heterogeneous `PathP` statement
-- follows by `J`-elimination on the K-path.
-- ============================================================================
module HoTTOperads.Operad.HLevel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; iso)
open import Cubical.Foundations.Equiv using (idEquiv ; equivFun)
open import Cubical.Foundations.Structure using (⟨_⟩)
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe ℓk : Level

module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  -- Σ-presentation of `Operad 𝒰 K`. The six fields of the record bundled
  -- as a nested Σ-type in the order they appear in `Operad/Base.agda`.
  OperadΣ : (K : Code → Type ℓk) → Type (ℓ-max (ℓ-max ℓc ℓe) ℓk)
  OperadΣ K =
    Σ[ isSetK ∈ ((A : Code) → isSet (K A)) ]
    Σ[ id    ∈ K 𝜏 ]
    Σ[ compₒ ∈ ((A : Code) (B : El A → Code) → K A → ((a : El A) → K (B a)) → K (⅀ A B)) ]
    Σ[ idl   ∈ ((A : Code) (k : K A)
                → PathP (λ i → K (Inj (⅀Idl≃ A) i))
                        (compₒ 𝜏 (λ _ → A) id (λ _ → k)) k) ]
    Σ[ idr   ∈ ((A : Code) (k : K A)
                → PathP (λ i → K (Inj (⅀Idr≃ A) i))
                        (compₒ A (λ _ → 𝜏) k (λ _ → id)) k) ]
    ((A : Code) (B : El A → Code)
       (C : (a : El A) → El (B a) → Code)
       (k : K A) (ks : (a : El A) → K (B a))
       (kss : (a : El A) (b : El (B a)) → K (C a b))
     → PathP (λ i → K (Inj (⅀Assoc≃ A B C) i))
             (compₒ A (λ a → ⅀ (B a) (C a)) k
                       (λ a → compₒ (B a) (C a) (ks a) (kss a)))
             (compₒ (⅀ A B) (⅀Assoc-C' A B C)
                       (compₒ A B k ks)
                       (λ ab → kss (fst (equivFun (⟦⅀⟧ A B) ab))
                                   (snd (equivFun (⟦⅀⟧ A B) ab)))))

  -- Iso between the record and Σ presentations.
  OperadIsoΣ : (K : Code → Type ℓk) → Iso (Operad 𝒰 K) (OperadΣ K)
  Iso.fun (OperadIsoΣ K) O = isSetK , id , compₒ , idl , idr , assoc
    where open Operad O
  Iso.inv (OperadIsoΣ K) (s , i , c , il , ir , a) = record
    { isSetK = s ; id = i ; compₒ = c ; idl = il ; idr = ir ; assoc = a }
  Iso.rightInv (OperadIsoΣ K) _ = refl
  Iso.leftInv  (OperadIsoΣ K) _ = refl

  -- Each Σ-component of `OperadΣ K`, given the previous components, is an
  -- h-set: the propositional components by `isProp→isSet`, and the data
  -- components (`id`, `compₒ`) by `isSetK`.
  isSetOperadΣ : (K : Code → Type ℓk) → isSet (OperadΣ K)
  isSetOperadΣ K =
    isOfHLevelΣ 2 (isProp→isSet (isPropΠ (λ A → isPropIsSet))) (λ isSetK →
    isOfHLevelΣ 2 (isSetK 𝜏)                                    (λ _ →
    isOfHLevelΣ 2 (isSetΠ λ A → isSetΠ λ B → isSetΠ λ _ → isSetΠ λ _ → isSetK (⅀ A B))
                                                                 (λ _ →
    isOfHLevelΣ 2 (isProp→isSet
                     (isPropΠ λ A → isPropΠ λ _ →
                        isOfHLevelPathP' 1 (isSetK A) _ _))     (λ _ →
    isOfHLevelΣ 2 (isProp→isSet
                     (isPropΠ λ A → isPropΠ λ _ →
                        isOfHLevelPathP' 1 (isSetK A) _ _))     (λ _ →
                  isProp→isSet
                     (isPropΠ λ A → isPropΠ λ B → isPropΠ λ C →
                      isPropΠ λ _ → isPropΠ λ _ → isPropΠ λ _ →
                        isOfHLevelPathP' 1 (isSetK (⅀ (⅀ A B) (⅀Assoc-C' A B C))) _ _))))))

  -- Transport h-set-hood across the Iso.
  isSetOperad : (K : Code → Type ℓk) → isSet (Operad 𝒰 K)
  isSetOperad K = isOfHLevelRetractFromIso 2 (OperadIsoΣ K) (isSetOperadΣ K)

  -- Proposition 6.5 (Section 6, Generalised Operad Universes) — first part.
  -- The heterogeneous path space between two 𝒰-operads is propositional.
  -- Proof: J on the K-path reduces to `K-path = refl`, where the PathP
  -- collapses to a path in `Operad 𝒰 K` — propositional by `isSetOperad`.
  isPropOperadPathP :
    {K L : Code → Type ℓk}
    (K-path : K ≡ L)
    (Oᴷ : Operad 𝒰 K) (Oᴸ : Operad 𝒰 L)
    → isProp (PathP (λ i → Operad 𝒰 (K-path i)) Oᴷ Oᴸ)
  isPropOperadPathP {K = K} {L = L} K-path Oᴷ Oᴸ =
    J (λ L' (q : K ≡ L') → (Oᴸ' : Operad 𝒰 L')
                          → isProp (PathP (λ i → Operad 𝒰 (q i)) Oᴷ Oᴸ'))
      (λ Oᴸ' → isSetOperad K Oᴷ Oᴸ')
      K-path Oᴸ

  -- Proposition 6.5 (Section 6, Generalised Operad Universes) — corollary.
  -- The Σ-type of (h-set family, operad on it) is a 1-groupoid. The base
  -- `Code → hSet` is a groupoid (`isOfHLevelTypeOfHLevel`); the fibre
  -- `Operad 𝒰 (⟨ K _ ⟩)` is an h-set (`isSetOperad`), hence a groupoid.
  isGroupoid-Operad-Σ :
    isGroupoid (Σ[ K ∈ (Code → hSet ℓk) ] Operad 𝒰 (λ A → ⟨ K A ⟩))
  isGroupoid-Operad-Σ =
    isOfHLevelΣ 3
      (isOfHLevelΠ 3 (λ _ → isOfHLevelTypeOfHLevel 2))
      (λ K → isOfHLevelSuc 2 (isSetOperad (λ A → ⟨ K A ⟩)))
