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
--
-- After the IR definition itself, this module also provides:
--   * `Fiber A` — the fibre of `CodeOp K` over `A` (as a Σ-type).
--   * `isSetFiberCodeOp` — the constructive proof that every fibre is an
--     h-set; the explicit `δ`-cube construction follows FreeOperad.tex
--     §9, lines 180-217.
--   * `FreeOps'` — alias `Fiber`, the family that carries the operad
--     structure transported across the fiber equivalence (the operad
--     itself lives in `HoTTOperads.Free.IR`).
module HoTTOperads.Free.IR.Base where

open import Agda.Builtin.Cubical.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

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

  -- ============================================================================
  -- Fibres of CodeOp
  --
  -- The fibre of `CodeOp` over a code `A`: a tree `t : FreeOpsIR` together with
  -- a path witnessing `CodeOp t ≡ A`.
  -- ============================================================================
  Fiber : (A : Code) → Type (ℓ-max (ℓ-max ℓc ℓe) ℓk)
  Fiber A = Σ[ t ∈ FreeOpsIR ] CodeOp t ≡ A

  -- Constructive proof that the fibres of CodeOp are h-sets.
  -- Follows FreeOperad.tex §9, lines 180-217: the `set` constructor of
  -- FreeOpsIR is engineered so that `cong (cong CodeOp)` is invertible on
  -- parallel paths (via flipSquare), which is exactly the characterisation
  -- of `f` having h-set fibres.
  --
  -- Concretely: given two paths P, Q : (t₁ , p₁) ≡ (t₂ , p₂) in Fiber A, we
  -- explicitly construct a 3-cell δ in Code that fills the cube spanned by
  -- their projections βP, βQ in the β-direction and p₁, p₂ in the path
  -- direction, with j = i1 face fixed to A. The j = i0 face of δ is then the
  -- square `s : PathP (λ i → CodeOp (αP i) ≡ CodeOp (αQ i)) refl refl` that
  -- feeds into `set t₁ t₂ αP αQ s` to produce the FreeOpsIR-level α-path,
  -- and the IR clause `CodeOp (set ... s i j) = s j i` ties it all together
  -- definitionally.
  isSetFiberCodeOp : (A : Code) → isSet (Fiber A)
  isSetFiberCodeOp A (t₁ , p₁) (t₂ , p₂) P Q k l =
    γ k l , (λ j → δ k l j)
    where
      -- Σ-decomposition of P and Q.
      αP : t₁ ≡ t₂
      αP m = fst (P m)
      βP : PathP (λ m → CodeOp (αP m) ≡ A) p₁ p₂
      βP m = snd (P m)
      αQ : t₁ ≡ t₂
      αQ m = fst (Q m)
      βQ : PathP (λ m → CodeOp (αQ m) ≡ A) p₁ p₂
      βQ m = snd (Q m)

      -- The 3-cell in Code that simultaneously fills βP, βQ, p₁, p₂.
      -- At k = i0 the back face is βP, at k = i1 the front face is βQ,
      -- the left (l = i0) and right (l = i1) walls are p₁, p₂ and the
      -- top (j = i1) is A. The bottom (j = i0) face is the data Square
      -- that we feed into the `set` constructor below.
      δ : (k l j : I) → Code
      δ k l j = hcomp
        (λ m → λ
          { (k = i0) → βP l (j ∨ ~ m)
          ; (k = i1) → βQ l (j ∨ ~ m)
          ; (l = i0) → p₁ (j ∨ ~ m)
          ; (l = i1) → p₂ (j ∨ ~ m)
          ; (j = i1) → A
          })
        A

      -- The j = i0 face of δ, repackaged as the PathP `set` expects.
      -- s l k = δ k l i0; at l = i0/i1 reduces to p₁ 0 / p₂ 0 = CodeOp t₁ /
      -- CodeOp t₂ (the hcomp's (l = i0/i1) face at j = i0 contracts to the
      -- starts of p₁, p₂), satisfying the `refl refl` boundary of the PathP.
      s : PathP (λ l → CodeOp (αP l) ≡ CodeOp (αQ l)) refl refl
      s l k = δ k l i0

      -- The FreeOpsIR-level 2-cell witnessing αP ≡ αQ. By the IR clause
      -- `CodeOp (set ... s k l) = s l k`, we have CodeOp (γ k l) = δ k l i0
      -- definitionally — exactly what makes `λ j → δ k l j` typecheck at
      -- type CodeOp (γ k l) ≡ A.
      γ : αP ≡ αQ
      γ = set t₁ t₂ αP αQ s

  -- The operations of the free operad: fibres of CodeOp K, parameterised by
  -- codes. The operad structure itself is constructed in
  -- `HoTTOperads.Free.IR` by combining the direct IR `graft` with the
  -- HIT-equivalence-transported operad laws.
  FreeOps' : Code → Type (ℓ-max (ℓ-max ℓc ℓe) ℓk)
  FreeOps' = Fiber
