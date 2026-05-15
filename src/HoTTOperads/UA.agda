{-# OPTIONS --cubical #-}
-- Univalence-derived lemmas (`ua→→`, `ua→→inv`) used in the operadic-law
-- proofs of HoTTOperads.Operad.Endo. Supporting infrastructure for
-- Section 7 (Category of Operads); no paper-numbered content.
module HoTTOperads.UA where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

private
  variable
    ℓ ℓ' ℓ'' : Level

opaque
  -- The action of ua on a function-typed family: when ua applied to an equivalence
  -- e : X₁ ≃ X₂ appears twice to the left of the function arrow,
  -- the heterogeneous path between f : (X₁ → Y) → Z and (λ ys → f (ys ∘ fun e))
  -- is given by ua-gluePt. Reference: Category.tex lines 119-123.
  ua→→ : {X₁ X₂ : Type ℓ} {Y : Type ℓ'} {Z : Type ℓ''}
         (f : (X₁ → Y) → Z) (e : X₁ ≃ X₂)
       → PathP (λ i → (ua e i → Y) → Z) f (λ ys → f (ys ∘ equivFun e))
  ua→→ f e i ys = f (ys ∘ ua-gluePt e i)

  -- ua→→ "in the inverse direction": given k : (X₂ → Y) → Y and e : X₁ ≃ X₂,
  -- construct a heterogeneous path from the precomposition (λ xs → k (xs ∘ invEq e))
  -- at the X₁ end to k itself at the X₂ end, along ua e. We obtain this by applying
  -- ua→→ to (invEquiv e), reversing direction with symP, and using uaInvEquiv to
  -- rewrite the index path back to ua e.
  ua→→inv : {X₁ X₂ : Type ℓ} {Y : Type ℓ'}
            (e : X₁ ≃ X₂) (k : (X₂ → Y) → Y)
          → PathP (λ i → (ua e i → Y) → Y)
                  (λ xs → k (xs ∘ invEq e)) k
  ua→→inv {Y = Y} e k =
    subst (λ p → PathP (λ i → (p (~ i) → Y) → Y) (λ xs → k (xs ∘ invEq e)) k)
          (uaInvEquiv e)
          (symP (ua→→ k (invEquiv e)))
