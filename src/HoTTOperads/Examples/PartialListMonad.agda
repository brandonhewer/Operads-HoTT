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
open import Cubical.Data.Bool using (Bool ; true ; false ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (isOfHLevelList)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (pred-≤-pred ; ¬-<-zero)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Fin.Properties using (Fin-fst-≡)
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
  -- in the new slot. Matches the `pokeM` lifting in Example 8.4
  -- (Section 8, Monad over an Operad).
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

  -- ------------------------------------------------------------------------
  -- Example 8.4 (Section 8, Monad over an Operad) — the round-trip path.
  --
  -- Selecting elements of `xs` and then putting them back unchanged —
  -- filling each hole with the singleton list of its stored element —
  -- recovers the original list. This is the paper's claim
  -- `runAlg fill⇒ ([_] <$> select p xs) ≡ xs`.
  --
  -- Proof by induction on `xs`. `consM` keeps the element in the partial
  -- list, so `fill` re-emits it (the cons case is definitional); `pokeM`
  -- stores it in a fresh hole, so `fill` re-emits it as the head of
  -- `[ a ] ++ …` (the poke case re-indexes the stored data along `fsuc`,
  -- a `Fin`-first-projection identity).
  -- ------------------------------------------------------------------------
  private
    isSetListA : isSet (List A)
    isSetListA = isOfHLevelList 0 isSetA

    RA : OpM O (List A) → List A
    RA = runAlg O (List A) isSetListA (fill⇒ isSetA)

    singletons : OpM O A → OpM O (List A)
    singletons o = (λ a → a ∷ []) <$> o

    -- A `consM`-prepended element is re-emitted by `fill` definitionally.
    H-cons : (a : A) (o : OpM O A)
           → RA (singletons (consM a o)) ≡ a ∷ RA (singletons o)
    H-cons a (i ▷ k ▷ d) = refl

    -- A `pokeM`-stored element is re-emitted as the head of its hole's
    -- singleton fill; the remaining data is re-indexed along `fsuc`.
    H-poke : (a : A) (o : OpM O A)
           → RA (singletons (pokeM a o)) ≡ a ∷ RA (singletons o)
    H-poke a (i ▷ k ▷ d) =
      cong (a ∷_)
        (cong (λ d' → RA (singletons (i ▷ k ▷ d')))
              (funExt (λ j → cong d (Fin-fst-≡ refl))))

  -- The round-trip identity itself (stated as in the paper).
  select-fill-id : (p : A → Bool) (xs : List A)
                 → runAlg O (List A) isSetListA (fill⇒ isSetA)
                          ((λ a → a ∷ []) <$> select p xs)
                 ≡ xs
  select-fill-id p []       = refl
  select-fill-id p (a ∷ as) with p a
  ... | true  = H-poke a (select p as) ∙ cong (a ∷_) (select-fill-id p as)
  ... | false = H-cons a (select p as) ∙ cong (a ∷_) (select-fill-id p as)
