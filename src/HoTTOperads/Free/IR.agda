{-# OPTIONS --cubical #-}
-- Inductive-recursive presentation of the free 𝒰-operad's operations
-- (FreeOperad.tex §9, lines 144-218).
--
-- Mutual `data`/`function`:
--   * leaf, node are the data constructors of FreeOpsIR
--   * `set` is the paper's higher path coherence (FreeOperad.tex line 205-207):
--       set p q : PathP (λ i → CodeOp K (p i) ≡ CodeOp K (q i)) refl refl → p ≡ q
--     This is a coherence on `cong CodeOp`, NOT a path constructor of FreeOpsIR.
--     It asserts that the fibres of `CodeOp` are h-sets (without forcing
--     FreeOpsIR itself to be an h-set).
module HoTTOperads.Free.IR where

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)

open import HoTTOperads.Universe.Base

private
  variable
    ℓc ℓe ℓk : Level

module _ {𝒰 : Universe ℓc ℓe} (K : Universe.Code 𝒰 → Type ℓk) where
  open Universe 𝒰

  data FreeOpsIR : Type (ℓ-max (ℓ-max ℓc ℓe) ℓk)
  CodeOp : FreeOpsIR → Code

  data FreeOpsIR where
    leaf : FreeOpsIR
    node : (A : Code) → K A → (El A → FreeOpsIR) → FreeOpsIR
    set : (t u : FreeOpsIR) (p q : t ≡ u)
        → PathP (λ i → CodeOp (p i) ≡ CodeOp (q i)) refl refl
        → p ≡ q

  CodeOp leaf                = 𝜏
  CodeOp (node A k ts)       = ⅀ A (CodeOp ∘ ts)
  CodeOp (set t u p q s i j) = s j i
