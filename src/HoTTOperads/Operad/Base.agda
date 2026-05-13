{-# OPTIONS --cubical #-}
module HoTTOperads.Operad.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv

open import HoTTOperads.Universe.Base

private
  variable
    ℓc ℓe ℓk : Level

-- A generalised 𝒰-operad on a family of h-sets K : Code 𝒰 → Type ℓk.
-- The fields encode:
--   id   : the unit operation at the unit code 𝜏,
--   compₒ : n-ary compₒosition with respect to ⅀ A B,
--   idl  : left identity (heterogeneous path over Inj (⅀Idl≃)),
--   idr  : right identity (heterogeneous path over Inj (⅀Idr≃)),
--   assoc: associativity (heterogeneous path over Inj (⅀Assoc≃)).
record Operad {ℓc ℓe : Level} (𝒰 : Universe ℓc ℓe) (K : Universe.Code 𝒰 → Type ℓk)
              : Type (ℓ-max (ℓ-max ℓc ℓe) ℓk) where
  open Universe 𝒰

  field
    isSetK : (A : Code) → isSet (K A)
    id     : K 𝜏
    compₒ   : (A : Code) (B : El A → Code)
           → K A → ((a : El A) → K (B a)) → K (⅀ A B)

    idl : (A : Code) (k : K A)
        → PathP (λ i → K (Inj (⅀Idl≃ A) i))
                (compₒ 𝜏 (λ _ → A) id (λ _ → k)) k

    idr : (A : Code) (k : K A)
        → PathP (λ i → K (Inj (⅀Idr≃ A) i))
                (compₒ A (λ _ → 𝜏) k (λ _ → id)) k

    assoc : (A : Code) (B : El A → Code)
            (C : (a : El A) → El (B a) → Code)
            (k : K A) (ks : (a : El A) → K (B a))
            (kss : (a : El A) (b : El (B a)) → K (C a b))
          → PathP (λ i → K (Inj (⅀Assoc≃ A B C) i))
                  (compₒ A (λ a → ⅀ (B a) (C a)) k
                        (λ a → compₒ (B a) (C a) (ks a) (kss a)))
                  (compₒ (⅀ A B) (⅀Assoc-C' A B C)
                        (compₒ A B k ks)
                        (λ ab → kss (fst (equivFun (⟦⅀⟧ A B) ab))
                                    (snd (equivFun (⟦⅀⟧ A B) ab))))
