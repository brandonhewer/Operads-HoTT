{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Monad.TwoCellCoherence
--
-- Genuine 2-cell coherence for the monad `OpM O` on h-groupoids, proved as
-- honest 2-paths (not discharged by truncation).
--
-- Every monad-law path is a triple `Inj e ▷ idl/idr/assoc ▷ data`. The
-- operadic (`Op`) component is a `PathP` over the h-set family `K`, hence
-- propositional; the `Index` component is `Inj` of a structure equivalence;
-- the `Data` component is a reindexing of the decoration.
--
-- `unit-triangle` (VERIFIED) is the pseudomonad unit-coherence triangle: the
-- two monad unit laws agree at the unit. It is proved genuinely: the `Index`
-- 2-path is `propEquivEq` (the equivalences `⅀Idl≃ 𝜏`, `⅀Idr≃ 𝜏` are
-- between the *propositions* `El (⅀ 𝜏 (λ _ → 𝜏))` and `El 𝜏`), the `Op`
-- 2-path is `isSet→SquareP` (h-set family `K`), and the `Data` 2-path is the
-- constant `y` path (`J`/`substRefl`, since `return`'s decoration is
-- constant). No groupoid-truncation is used.
--
-- `join`-naturality is *definitional* here (`_<$>_` is index-preserving):
-- `g <$> join O z ≡ join O ((g <$>_) <$> z)` holds by `refl`
-- (`join-natural`). `route-L` is one of the two parallel reassociation
-- 2-paths of the associativity pentagon at `T⁴`.
--
-- Formalises from the paper:
--   Section 8 (Monad over an Operad), Theorem 8.2 — the 2-cell coherence of
--   the h-groupoid-restricted monad.
-- ============================================================================
module HoTTOperads.Monad.TwoCellCoherence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels using (isSet→SquareP)
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Univalence using (ua)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived using (propEquivEq ; isPropEl𝜏 ; isPropEl-⅀𝜏𝜏)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Composition using (return ; join)
open import HoTTOperads.Monad.Functor using (_<$>_)
open import HoTTOperads.Monad.Laws using (join-return₁ ; join-return₂ ; join-assoc)

private
  variable
    ℓc ℓe ℓk ℓx : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk}
         (O : Operad 𝒰 K) where
  open Universe 𝒰
  open Operad O

  opaque
    unfolding join-return₁ join-return₂

    -- ------------------------------------------------------------------------
    -- Pseudomonad unit triangle (VERIFIED): the two monad unit laws agree at
    -- the unit. At `return O y` both unit laws are paths
    --   join O (return O (return O y)) ≡ return O y
    -- (`return O <$> return O y` and `return O (return O y)` are
    -- definitionally equal). Each is a triple `Inj e ▷ idl/idr ▷ data`,
    -- with `e ∈ {⅀Idl≃ 𝜏, ⅀Idr≃ 𝜏}` — equivalences between the
    -- propositions `El (⅀ 𝜏 (λ _ → 𝜏))` and `El 𝜏`, hence equal by
    -- `propEquivEq`; the `Op` component a `PathP` over the h-set family `K`;
    -- the decoration `λ _ → y` constant, so its `data` component is the
    -- constant `PathP`. The triangle is the resulting square.
    -- ------------------------------------------------------------------------
    unit-triangle : {X : Type ℓx} (y : X)
                  → join-return₁ O (return O y) ≡ join-return₂ O (return O y)
    unit-triangle {X = X} y = jr₁≡c₁ ∙ middle ∙ sym jr₂≡c₂
      where
        c₁ : join O (return O (return O y)) ≡ return O y
        c₁ i = Inj (⅀Idl≃ 𝜏) i ▷ idl 𝜏 id i ▷ (λ _ → y)

        c₂ : join O (return O (return O y)) ≡ return O y
        c₂ i = Inj (⅀Idr≃ 𝜏) i ▷ idr 𝜏 id i ▷ (λ _ → y)

        dpEq₁ : PathP (λ _ → PathP (λ i → El (Inj (⅀Idl≃ 𝜏) i) → X)
                                   (λ _ → y) (λ _ → y))
                      (subst (λ p → PathP (λ i → p i → X) (λ _ → y) (λ _ → y))
                             (⟦⅀Idl⟧ 𝜏) (λ i _ → y))
                      (λ i _ → y)
        dpEq₁ = J (λ (b : El (⅀ 𝜏 (λ _ → 𝜏)) ≡ El 𝜏)
                     (q : ua (⅀Idl≃ 𝜏) ≡ b)
                   → subst (λ p → PathP (λ i → p i → X)
                                        (λ _ → y) (λ _ → y))
                           q (λ i _ → y)
                   ≡ (λ i (_ : b i) → y))
                  (substRefl {B = λ p → PathP (λ i → p i → X)
                                              (λ _ → y) (λ _ → y)}
                             {x = ua (⅀Idl≃ 𝜏)}
                             (λ i _ → y))
                  (⟦⅀Idl⟧ 𝜏)

        dpEq₂ : PathP (λ _ → PathP (λ i → El (Inj (⅀Idr≃ 𝜏) i) → X)
                                   (λ _ → y) (λ _ → y))
                      (subst (λ p → PathP (λ i → p i → X) (λ _ → y) (λ _ → y))
                             (⟦⅀Idr⟧ 𝜏) (λ i _ → y))
                      (λ i _ → y)
        dpEq₂ = J (λ (b : El (⅀ 𝜏 (λ _ → 𝜏)) ≡ El 𝜏)
                     (q : ua (⅀Idr≃ 𝜏) ≡ b)
                   → subst (λ p → PathP (λ i → p i → X)
                                        (λ _ → y) (λ _ → y))
                           q (λ i _ → y)
                   ≡ (λ i (_ : b i) → y))
                  (substRefl {B = λ p → PathP (λ i → p i → X)
                                              (λ _ → y) (λ _ → y)}
                             {x = ua (⅀Idr≃ 𝜏)}
                             (λ i _ → y))
                  (⟦⅀Idr⟧ 𝜏)

        jr₁≡c₁ : join-return₁ O (return O y) ≡ c₁
        jr₁≡c₁ j i = Inj (⅀Idl≃ 𝜏) i ▷ idl 𝜏 id i ▷ dpEq₁ j i

        jr₂≡c₂ : join-return₂ O (return O y) ≡ c₂
        jr₂≡c₂ j i = Inj (⅀Idr≃ 𝜏) i ▷ idr 𝜏 id i ▷ dpEq₂ j i

        idxSq : Inj (⅀Idl≃ 𝜏) ≡ Inj (⅀Idr≃ 𝜏)
        idxSq = cong Inj (propEquivEq (isPropEl-⅀𝜏𝜏 𝒰) (isPropEl𝜏 𝒰)
                                      (⅀Idl≃ 𝜏) (⅀Idr≃ 𝜏))

        opSq : SquareP (λ j i → K (idxSq j i))
                       (idl 𝜏 id) (idr 𝜏 id) refl refl
        opSq = isSet→SquareP (λ j i → isSetK (idxSq j i))
                             (idl 𝜏 id) (idr 𝜏 id) refl refl

        middle : c₁ ≡ c₂
        middle j i = idxSq j i ▷ opSq j i ▷ (λ (_ : El (idxSq j i)) → y)

  -- --------------------------------------------------------------------------
  -- Associativity pentagon at `T⁴`.
  --
  -- `join`-naturality is definitional here (`_<$>_` is index-preserving):
  -- `g <$> join O z ≡ join O ((g <$>_) <$> z)` by `refl`. `route-L` is one
  -- parallel reassociation 2-path of the pentagon. The operadic (`Op`) third
  -- of the pentagon 2-path is propositional by the same
  -- `isSet→SquareP`-over-`K` argument as the unit triangle; the remaining
  -- `Index`/`Data` glue (the Mac Lane pentagon for the universe associator
  -- `⅀Assoc≃`, lifted through `Inj`/`ua` by `InjComp`/`⟦⅀Assoc⟧`) is a
  -- development on the scale of `Free/HIT.agda`.
  -- --------------------------------------------------------------------------
  join-natural : {X Y : Type ℓx}
                 (g : OpM O (OpM O (OpM O X)) → Y)
                 (z : OpM O (OpM O (OpM O (OpM O (OpM O X)))))
               → g <$> (join O z) ≡ join O ((λ u → g <$> u) <$> z)
  join-natural g z = refl

  route-L : {X : Type ℓx} (w : OpM O (OpM O (OpM O (OpM O X))))
          → join O (join O (join O w))
          ≡ join O ((join O) <$> ((join O) <$> w))
  route-L w = cong (join O) (join-assoc O w)
            ∙ join-assoc O ((join O) <$> w)
