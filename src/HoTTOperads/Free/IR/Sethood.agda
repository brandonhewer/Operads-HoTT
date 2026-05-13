{-# OPTIONS --cubical #-}
-- Constructive proof that the fibres of CodeOp K are h-sets.
-- Follows FreeOperad.tex §9, lines 180-217: the `set` constructor of FreeOpsIR
-- is engineered so that `cong (cong CodeOp)` is invertible on parallel paths
-- (via flipSquare), which is exactly the characterisation of f having h-set
-- fibres.
--
-- Concretely: given two paths P, Q : (t₁ , p₁) ≡ (t₂ , p₂) in Fiber A, we
-- explicitly construct a 3-cell δ in Code that fills the cube spanned by
-- their projections βP, βQ in the β-direction and p₁, p₂ in the path
-- direction, with j = i1 face fixed to A. The j = i0 face of δ is then the
-- square `s : PathP (λ i → CodeOp (αP i) ≡ CodeOp (αQ i)) refl refl` that
-- feeds into `set t₁ t₂ αP αQ s` to produce the FreeOpsIR-level α-path,
-- and the IR clause `CodeOp (set ... s i j) = s j i` ties it all together
-- definitionally.
module HoTTOperads.Free.IR.Sethood where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Free.IR

private
  variable
    ℓc ℓe ℓk : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} where
  open Universe 𝒰

  -- Fibre of CodeOp K over A : Code.
  Fiber : (A : Code) → Type (ℓ-max (ℓ-max ℓc ℓe) ℓk)
  Fiber A = Σ[ t ∈ FreeOpsIR {𝒰 = 𝒰} K ] CodeOp K t ≡ A

  isSetFiberCodeOp : (A : Code) → isSet (Fiber A)
  isSetFiberCodeOp A (t₁ , p₁) (t₂ , p₂) P Q k l =
    γ k l , (λ j → δ k l j)
    where
      -- Σ-decomposition of P and Q.
      αP : t₁ ≡ t₂
      αP m = fst (P m)
      βP : PathP (λ m → CodeOp K (αP m) ≡ A) p₁ p₂
      βP m = snd (P m)
      αQ : t₁ ≡ t₂
      αQ m = fst (Q m)
      βQ : PathP (λ m → CodeOp K (αQ m) ≡ A) p₁ p₂
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
      s : PathP (λ l → CodeOp K (αP l) ≡ CodeOp K (αQ l)) refl refl
      s l k = δ k l i0

      -- The FreeOpsIR-level 2-cell witnessing αP ≡ αQ. By the IR clause
      -- `CodeOp (set ... s k l) = s l k`, we have CodeOp K (γ k l) = δ k l i0
      -- definitionally — exactly what makes `λ j → δ k l j` typecheck at
      -- type CodeOp K (γ k l) ≡ A.
      γ : αP ≡ αQ
      γ = set t₁ t₂ αP αQ s
