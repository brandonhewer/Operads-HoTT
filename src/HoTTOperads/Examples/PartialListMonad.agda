{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Examples.PartialListMonad
--
-- The monad over the PartialList operad as a programming idiom: `consM`
-- lifts `_∷_`, `pokeM` lifts `poke`, `select` filters a list by turning
-- predicate hits into holes, and `mapWhere` interprets the result through
-- the `fill` algebra to recover a concrete `List A`.
--
-- Formalises from the paper:
--   Example 8.4 (Section 8, Monad over an Operad) — `select` and `mapWhere`.
-- ============================================================================
module HoTTOperads.Examples.PartialListMonad where

open import Cubical.Foundations.Prelude hiding (fill)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Bool using (Bool ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (pred-≤-pred ; ¬-<-zero)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Empty using () renaming (rec to ⊥-rec)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Instances.Nat using (𝓝)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Endo using (Endo)
open import HoTTOperads.Examples.PartialList
open import HoTTOperads.Examples.PartialListAlgebra using (fill⇒)
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Functor using (_<$>_)
open import HoTTOperads.Monad.Algebra using (runAlg)

private
  variable
    ℓ : Level

module _ {A : Type ℓ} (isSetA : isSet A) where
  private
    O = PartialListOperad A isSetA

  -- Monadic lifting of `_∷_`. Preserves the index; just prepends `a` to the operation.
  consM : {X : Type ℓ} → A → OpM O X → OpM O X
  consM a (i ▷ k ▷ d) = i ▷ (a ∷ k) ▷ d

  -- Cons a new "head" value onto the decoration of an OpM, used by pokeM below.
  pokeData : {X : Type ℓ} {i : ℕ} → X → (Fin i → X) → Fin (suc i) → X
  pokeData x d (zero  , _) = x
  pokeData x d (suc j , p) = d (j , pred-≤-pred p)

  -- Monadic lifting of `poke`. Bumps the arity, prepends a hole, and stores `x`
  -- in the new slot. Matches Monads.tex lines 199-201.
  pokeM : {X : Type ℓ} → X → OpM O X → OpM O X
  pokeM x (i ▷ k ▷ d) = suc i ▷ poke k ▷ pokeData x d

  -- Example 8.4 (Section 8, Monad over an Operad) — `select`.
  -- Filter `xs` by `p`. Selected elements become holes (via pokeM); rejected
  -- elements stay in the list (via consM).
  select : (A → Bool) → List A → OpM O A
  select p []       = 0 ▷ [] ▷ λ { (_ , k<0) → ⊥-rec (¬-<-zero k<0) }
  select p (a ∷ as) = if p a then pokeM a (select p as) else consM a (select p as)

  -- Example 8.4 (Section 8, Monad over an Operad) — `mapWhere`.
  -- Apply `f` to every element of `xs` that matches `p`; pass the rest
  -- through unchanged. Built from `select` (puts hits into holes) and the
  -- `fill` algebra (concatenates the filling lists back together), with the
  -- functor action `_<$>_` mapping each hit through `f` packaged as a
  -- singleton list `[ f a ]`.
  mapWhere : (A → Bool) → (A → A) → List A → List A
  mapWhere p f xs =
    runAlg O (List A) (isOfHLevelList 0 isSetA)
            (fill⇒ isSetA)
            ((λ a → f a ∷ []) <$> select p xs)
