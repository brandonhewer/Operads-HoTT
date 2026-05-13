{-# OPTIONS --cubical #-}
-- Monad over the PartialList operad — illustrates how OpM (PartialListOperad A)
-- gives a useful programming idiom: `consM` lifts `_∷_`, `pokeM` lifts `poke`,
-- and `select` filters a list by turning predicate hits into holes.
module HoTTOperads.Examples.PartialListMonad where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Bool using (Bool ; if_then_else_)
open import Cubical.Data.List using (List ; [] ; _∷_)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (pred-≤-pred ; ¬-<-zero)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Empty using () renaming (rec to ⊥-rec)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Instances.Nat using (𝓝)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Examples.PartialList
open import HoTTOperads.Monad.Base

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

  -- Filter `xs` by `p`. Selected elements become holes (via pokeM); rejected
  -- elements stay in the list (via consM). Matches Monads.tex lines 212-216.
  select : (A → Bool) → List A → OpM O A
  select p []       = 0 ▷ [] ▷ λ { (_ , k<0) → ⊥-rec (¬-<-zero k<0) }
  select p (a ∷ as) = if p a then pokeM a (select p as) else consM a (select p as)
