{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Free.Universal
--
-- Constructive proof of the free-forgetful adjunction (FreeOperad.tex §9,
-- Theorem `thm:free-universal`). For each operad O on L and every species
-- morphism f : ∀ A → K A → L A, we exhibit:
--
--   * η     — unit of the adjunction at K
--   * interpret O f — operad morphism FreeOperad K ⇒ O extending f along η
--   * universal — contractibility of the type of such factorisations
--
-- All three are built constructively. The technical lemma `equivs-agree`
-- inside the `bridge` of `graft-eta` — comparing the two Code paths
-- `⅀AssocD ∙ ⅀-subst-path` and `cong (⅀ A) B-shape≡B` from `⅀ A B-shape`
-- to `⅀ A B` — is discharged via an `InjSec` sandwich whose central
-- `pathToEquiv`-equality is built pointwise on canonical pairs
-- `invEq (⟦⅀⟧ A B-shape) (a, w)`: `LHS-chain` reduces the LHS transport
-- via `transp-⅀AssocD-pair + transp-⅀-subst-path + secEq`; `RHS-chain`
-- reduces the RHS transport via `⟦⅀⟧-natural-snd + secEq`; `pair-eq`
-- glues the two outputs via `b₀ ≡ α` (by `isPropEl𝜏`) and a heterogeneous
-- `subst-filler ∙ subst-filler ▷ shift3` cell, with `shift3` inverting
-- `transp-⅀IdlD` via `transport⁻Transport`.
--
-- ## Strategy
--
--   §1  `η`, defined as `subst (FreeOps K) (Inj (⅀Idr≃ A)) (node A (λ _ → 𝜏) k
--       (λ _ → leaf))`, the HIT-transported form of the paper's IR-style
--       `(node A k (λ _ → leaf), ⅀Idr 𝒰 A)`.
--
--   §2  `graft-eta : graft A B (η A k) ts ≡ node A B k ts`. Standalone (only
--       depends on the universe and `K`, not on the operad `O` or `f`); used
--       by §8's uniqueness argument to rewrite `node` as `graft (η _) _`.
--       Structure: `graft-subst-fst` to push the η-subst past the inner
--       `graft`, `substComposite` to merge the two outer substs, then a
--       Code-level `bridge` (`InjSec` sandwich + the canonical-pair
--       `equivs-agree` proof described above) to align the path with
--       `cong (⅀ A) B-shape≡B`, finally `subst-cong-⅀-node` + `ts-correct`.
--
--   §3  The underlying map `interp` of `interpret`, by direct pattern-match
--       on `FreeOps`. `on-id` is `refl` definitionally; `on-comp` is the
--       lemma `interp-graft` proved in §5.
--
--   §4  `interp-subst` — subst-naturality, a one-line invocation of the
--       library's `substCommSlice`.
--
--   §5  `interp-graft : interp (graft t ts) ≡ comp-O (interp t) (interp ∘ ts)`.
--       Induction on `t`. Cases:
--         leaf  — uses `idl-O` and the `⅀IdlD = sym(Inj ⅀Idl≃) ∙ cong (⅀ 𝜏) B-const`
--                 decomposition.
--         node  — uses `assoc-O`, the IH, and a `final-PathP` heterogeneous
--                 cell varying both the codomain family along `C'-eq` and
--                 the per-fibre values along `tss-PathP`.
--         set   — prop fill in the h-set `L (⅀ A B)`.
--
--   §6  `interpret` — assembled as a `_⇒_` record: `⟪_⟫ = interp`,
--       `on-id = refl`, `on-comp = interp-graft`.
--
--   §7  `η-correct` — interp commutes with η: `interp A (η A k) ≡ f A k`.
--       One-shot use of `interp-subst` + `fromPathP (idr-O A (f A k))`.
--
--   §8  `agree` (pointwise uniqueness against any other extension) and
--       `morphism-≡` (Σ-extensionality on operad morphisms).
--
--   §9  `universal` — contractibility of `Σ[ g ∈ FreeOperad K ⇒ O ] (g η ≡ f)`,
--       with center `(interpret O f , η-correct)`. Establishes the universal
--       property of `FreeOperad K` as left adjoint to the forgetful functor
--       from 𝒰-operads to 𝒰-species at K.
-- ============================================================================
module HoTTOperads.Free.Universal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path using (isProp→SquareP)
open import Cubical.Foundations.Transport using (substComposite ; substCommSlice ; transport⁻Transport)
open import Cubical.Foundations.GroupoidLaws using (lUnit ; rUnit ; lCancel ; rCancel ; assoc ; congFunct)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; uaCompEquiv ; pathToEquiv ; pathToEquivRefl ; pathToEquiv-ua)
open import Cubical.Data.Sigma using (Σ-syntax ; _,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-snd)
open import Cubical.Data.Unit using (tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived
open import HoTTOperads.Universe.IRDerived
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Morphism
open import HoTTOperads.Free.HIT

private
  variable
    ℓc ℓe ℓk ℓl : Level

module _ {𝒰 : Universe ℓc ℓe} (K : Universe.Code 𝒰 → Type ℓk) where
  open Universe 𝒰

  -- ============================================================================
  -- §1  η — unit of the adjunction
  --
  -- Paper (FreeOperad.tex:350): η A k = (node A k (λ _ → leaf), ⅀Idr 𝒰 A).
  -- In the HIT presentation, `node A B k ts : FreeOps K (⅀ A B)`, so the
  -- "(_, ⅀Idr 𝒰 A)" projection becomes a `subst` along `Inj (⅀Idr≃ A)`.
  -- ============================================================================
  η : (A : Code) → K A → FreeOps {𝒰 = 𝒰} K A
  η A k = subst (FreeOps {𝒰 = 𝒰} K) (Inj (⅀Idr≃ A))
                (node A (λ _ → 𝜏) k (λ _ → leaf))

  -- A PathP avatar of η, the heterogeneous version of the `subst` definition
  -- above. Definitionally `toPathP refl`. Provided as public API for clients
  -- that need to align η-substed values with `Inj (⅀Idr≃ A)`-indexed PathPs.
  η-PathP : (A : Code) (k : K A)
          → PathP (λ i → FreeOps {𝒰 = 𝒰} K (Inj (⅀Idr≃ A) i))
                  (node A (λ _ → 𝜏) k (λ _ → leaf)) (η A k)
  η-PathP A k = toPathP refl

  -- ============================================================================
  -- §2  `graft-eta` — `graft A B (η A k) ts ≡ node A B k ts`.
  --
  -- Consumed by §8's uniqueness argument: every `node A B k ts` is expressible
  -- as `graft A B (η A k) ts`, so an operad morphism's `on-comp` determines its
  -- value on `node` from its value on `η`.
  --
  -- Proof structure (mirrors `graft-idr`'s node-case bridge in
  -- HIT.agda:627-743, but with the second leg of the bridge being
  -- `⅀-subst-path p B` instead of `Inj (⅀Idr≃ (⅀ A B))`):
  --   (1) `graft-subst-fst` pushes the outer subst (from η) past the graft.
  --   (2) `substComposite` collapses the two outer substs into one composite
  --       along `⅀AssocD ∙ ⅀-subst-path`.
  --   (3) `bridge` rewrites that composite as `cong (⅀ A) B-shape≡B` via the
  --       `InjSec` sandwich, with the equivalence-equality `equivs-agree`
  --       proved pointwise on canonical pairs (see header comment).
  --   (4) `subst-cong-⅀-node` distributes the resulting subst over `node`,
  --       turning it into per-fibre substs along `funExt⁻ B-shape≡B a`.
  --   (5) `ts-correct` collapses each per-fibre subst back to `ts a`, using
  --       `rCancel` on the `⅀IdlD ∙ sym ⅀IdlD` pair embedded in `per-fibre a`
  --       and `apd ts (e a)` for the `cong B (e a)` leg.
  -- ============================================================================
  module _ where
    private
      α : El 𝜏
      α = invEq ⟦𝜏⟧ tt

    -- Restructured proof using a 2-leg bridge (no `cong (⅀ A) q-eq` leg):
    -- avoid the initial `sym (subst-cong-⅀-node)` step by combining only
    -- `⅀AssocD ∙ ⅀-subst-path` and bridging to `cong (⅀ A) B-shape≡B`. The
    -- per-fibre `⅀IdlD` cancellation is then absorbed into `ts-correct`.
    graft-eta : (A : Code) (B : El A → Code) (k : K A)
                (ts : (a : El A) → FreeOps {𝒰 = 𝒰} K (B a))
              → graft K A B (η A k) ts ≡ node A B k ts
    graft-eta A B k ts =
        graft-subst-fst {𝒰 = 𝒰} K p B (node A (λ _ → 𝜏) k (λ _ → leaf)) ts
      ∙ -- Collapse the two outer substs into one composite. The inner graft
        -- has reduced (definitionally) to a `subst` over `⅀AssocD`.
        sym (substComposite (FreeOps {𝒰 = 𝒰} K)
                             (⅀AssocD 𝒰 A (λ _ → 𝜏) B-tp)
                             (⅀-subst-path {𝒰 = 𝒰} p B)
                             (node A B-shape k per-fibre))
      ∙ -- Bridge `⅀AssocD ∙ ⅀-subst-path` to `cong (⅀ A) B-shape≡B`.
        cong (λ pp → subst (FreeOps {𝒰 = 𝒰} K) pp (node A B-shape k per-fibre)) bridge
      ∙ -- Apply `subst-cong-⅀-node` forward; the family path is absorbed.
        subst-cong-⅀-node {𝒰 = 𝒰} K A B-shape≡B k per-fibre
      ∙ -- The per-fibre subst equals `ts` pointwise.
        cong (node A B k) ts-correct
      where
        p : ⅀ A (λ _ → 𝜏) ≡ A
        p = Inj (⅀Idr≃ A)

        B-tp : El (⅀ A (λ _ → 𝜏)) → Code
        B-tp a = B (transport (cong El p) a)

        paired1 : (a : El A) → El 𝜏 → El (⅀ A (λ _ → 𝜏))
        paired1 a b = invEq (⟦⅀⟧ A (λ _ → 𝜏)) (a , b)

        -- Family at the inner `node` (after graft-on-node reduction).
        B-shape : El A → Code
        B-shape a = ⅀ 𝜏 (λ b → B-tp (paired1 a b))

        -- Per-fibre subtrees after graft-on-leaf reduction inside `node`.
        per-fibre : (a : El A) → FreeOps {𝒰 = 𝒰} K (B-shape a)
        per-fibre a = subst (FreeOps {𝒰 = 𝒰} K)
                            (⅀IdlD 𝒰 (λ b → B-tp (paired1 a b)))
                            (ts (transport (cong El p) (paired1 a α)))

        -- Per-fibre `⅀Idr≃`-secEq computation.
        e : (a : El A) → transport (cong El p) (paired1 a α) ≡ a
        e a =
            cong (transport (cong El p)) (invEq-⅀Idr A a)
          ∙ cong (λ pp → transport pp (invEq (⅀Idr≃ A) a)) (sym (⟦⅀Idr⟧ A))
          ∙ uaβ (⅀Idr≃ A) (invEq (⅀Idr≃ A) a)
          ∙ secEq (⅀Idr≃ A) a

        -- Family path B-shape ≡ B. Per fibre: sym(⅀IdlD) cancels the ⅀-wrap,
        -- and cong B of `e a` adjusts the index from `transport p (paired1 a α)`
        -- to `a`.
        B-shape≡B : B-shape ≡ B
        B-shape≡B = funExt (λ a → sym (⅀IdlD 𝒰 (λ b → B-tp (paired1 a b)))
                                ∙ cong B (e a))

        -- The bridge proof: `⅀AssocD ∙ ⅀-subst-path ≡ cong (⅀ A) B-shape≡B`.
        --
        -- Both Code paths go from `⅀ A B-shape` to `⅀ A B`. We use the
        -- `InjSec` sandwich: both paths, when injected via
        -- `Inj ∘ pathToEquiv ∘ cong El`, recover themselves. The induced
        -- equivalences on `El` are shown equal by `equivEq + funExt`,
        -- reducing pointwise on the canonical Σ-pair `invEq (⟦⅀⟧ A B-shape) (a, w)`.
        --
        --   * `LHS-chain` reduces `transport (cong El lhs-path) (canonical-pair)`
        --     to `invEq (⟦⅀⟧ A B) (transport p (paired1 a b₀) , v₀)` via
        --     `transp-⅀AssocD-pair` then `transp-⅀-subst-path` then `secEq`.
        --   * `RHS-chain` reduces `transport (cong El rhs-path) (canonical-pair)`
        --     to `invEq (⟦⅀⟧ A B) (a , transport (cong El (funExt⁻ B-shape≡B a)) w)`
        --     via `⟦⅀⟧-natural-snd` then `secEq`.
        --   * `pair-eq` glues the two via `b₀ ≡ α` (by `isPropEl𝜏`) on the
        --     first coord and a heterogeneous `subst-filler ∙ subst-filler ▷ shift3`
        --     on the second; `shift3` uses `transport⁻Transport` to invert
        --     `transp-⅀IdlD`.
        bridge : ⅀AssocD 𝒰 A (λ _ → 𝜏) B-tp ∙ ⅀-subst-path {𝒰 = 𝒰} p B
               ≡ cong (⅀ A) B-shape≡B
        bridge =
            sym (InjSec 𝒰 lhs-path)
          ∙ cong Inj equivs-agree
          ∙ InjSec 𝒰 rhs-path
          where
            lhs-path = ⅀AssocD 𝒰 A (λ _ → 𝜏) B-tp ∙ ⅀-subst-path {𝒰 = 𝒰} p B
            rhs-path = cong (⅀ A) B-shape≡B

            -- Per-(a,w) decomposition of the canonical pre-image of `w` under
            -- `⟦⅀⟧ 𝜏 (B-tp ∘ paired1 a)`. `b₀-of` is the `El 𝜏`-coord (always
            -- propositionally `α`); `v₀-of` is the per-fibre value.
            b₀-of : (a : El A) (w : El (B-shape a)) → El 𝜏
            b₀-of a w = fst (equivFun (⟦⅀⟧ 𝜏 (λ b → B-tp (paired1 a b))) w)

            v₀-of : (a : El A) (w : El (B-shape a))
                  → El (B-tp (paired1 a (b₀-of a w)))
            v₀-of a w = snd (equivFun (⟦⅀⟧ 𝜏 (λ b → B-tp (paired1 a b))) w)

            b₀≡α : (a : El A) (w : El (B-shape a)) → b₀-of a w ≡ α
            b₀≡α a w = isPropEl𝜏 𝒰 (b₀-of a w) α

            -- Reduction of the LHS transport on canonical pairs. Steps:
            --   (1) `congFunct + substComposite` split the composite path.
            --   (2) `transp-⅀AssocD-pair` handles the inner ⅀AssocD-leg.
            --   (3) `transp-⅀-subst-path` handles the outer ⅀-subst-path-leg.
            --   (4) `secEq (⟦⅀⟧ (⅀ A (λ _ → 𝜏)) B-tp)` cancels `equivFun ∘ invEq`.
            LHS-chain : (a : El A) (w : El (B-shape a))
                      → transport (cong El lhs-path)
                                  (invEq (⟦⅀⟧ A B-shape) (a , w))
                      ≡ invEq (⟦⅀⟧ A B)
                              (transport (cong El p) (paired1 a (b₀-of a w))
                              , v₀-of a w)
            LHS-chain a w =
                cong (λ q → transport q (invEq (⟦⅀⟧ A B-shape) (a , w)))
                     (congFunct El (⅀AssocD 𝒰 A (λ _ → 𝜏) B-tp)
                                   (⅀-subst-path {𝒰 = 𝒰} p B))
              ∙ substComposite (λ X → X)
                               (cong El (⅀AssocD 𝒰 A (λ _ → 𝜏) B-tp))
                               (cong El (⅀-subst-path {𝒰 = 𝒰} p B))
                               (invEq (⟦⅀⟧ A B-shape) (a , w))
              ∙ cong (transport (cong El (⅀-subst-path {𝒰 = 𝒰} p B)))
                     (transp-⅀AssocD-pair {𝒰 = 𝒰} A (λ _ → 𝜏) B-tp a w)
              ∙ transp-⅀-subst-path {𝒰 = 𝒰} p B
                                     (invEq (⟦⅀⟧ (⅀ A (λ _ → 𝜏)) B-tp)
                                            (paired1 a (b₀-of a w) , v₀-of a w))
              ∙ cong (λ pair → invEq (⟦⅀⟧ A B)
                                     (transport (cong El p) (fst pair) , snd pair))
                     (secEq (⟦⅀⟧ (⅀ A (λ _ → 𝜏)) B-tp)
                            (paired1 a (b₀-of a w) , v₀-of a w))

            -- Reduction of the RHS transport on canonical pairs. Steps:
            --   (1) `⟦⅀⟧-natural-snd 𝒰 A B-shape≡B` factors the transport
            --       through `Σ-cong-equiv-snd` (using `equivFun (pathToEquiv P)
            --       ≡ transport P` definitionally to align `transport` with
            --       `equivFun (pathToEquiv …)`).
            --   (2) `secEq (⟦⅀⟧ A B-shape) (a , w)` cancels the inner
            --       `equivFun ∘ invEq`.
            RHS-chain : (a : El A) (w : El (B-shape a))
                      → transport (cong El rhs-path)
                                  (invEq (⟦⅀⟧ A B-shape) (a , w))
                      ≡ invEq (⟦⅀⟧ A B)
                              (a , transport (cong El (funExt⁻ B-shape≡B a)) w)
            RHS-chain a w =
                cong (λ ee → equivFun ee (invEq (⟦⅀⟧ A B-shape) (a , w)))
                     (⟦⅀⟧-natural-snd 𝒰 A B-shape≡B)
              ∙ cong (λ pair → invEq (⟦⅀⟧ A B)
                                     ( fst pair
                                     , transport (cong El (funExt⁻ B-shape≡B (fst pair)))
                                                 (snd pair)))
                     (secEq (⟦⅀⟧ A B-shape) (a , w))

            -- The Σ-pair-equality bridging `LHS-chain`'s output to `RHS-chain`'s
            -- output. Both pairs live in `Σ (El A) (λ a' → El (B a'))`.
            --   * `eq-fst` shifts the first coord via `b₀ ≡ α` (by `isPropEl𝜏`)
            --     followed by `e a` (the `secEq`-driven cancellation of `paired1`
            --     against `transport (cong El p)`).
            --   * `eq-snd` is a heterogeneous PathP over `eq-fst` built as
            --     `compPathP' shift1 shift2 ▷ shift3`, where `shift1`/`shift2`
            --     are subst-fillers for `b₀≡α`/`e a` and `shift3` matches the
            --     post-shift value to `transport (cong El (funExt⁻ B-shape≡B a)) w`
            --     via `congFunct + substComposite + transport⁻Transport` (the
            --     latter inverts `transp-⅀IdlD` after `b₀ ≡ α`-canonicalisation).
            pair-eq : (a : El A) (w : El (B-shape a))
                    → Path (Σ-syntax (El A) (λ a' → El (B a')))
                           (transport (cong El p) (paired1 a (b₀-of a w))
                           , v₀-of a w)
                           (a , transport (cong El (funExt⁻ B-shape≡B a)) w)
            pair-eq a w = ΣPathP (eq-fst , eq-snd)
              where
                D : El 𝜏 → Code
                D b = B-tp (paired1 a b)

                eq-fst : transport (cong El p) (paired1 a (b₀-of a w)) ≡ a
                eq-fst = cong (λ b → transport (cong El p) (paired1 a b)) (b₀≡α a w)
                       ∙ e a

                v₀-shifted-α : El (D α)
                v₀-shifted-α = subst (λ b → El (D b)) (b₀≡α a w) (v₀-of a w)

                shift1 : PathP (λ i → El (D (b₀≡α a w i)))
                               (v₀-of a w) v₀-shifted-α
                shift1 = subst-filler (λ b → El (D b)) (b₀≡α a w) (v₀-of a w)

                shift2 : PathP (λ i → El (B (e a i)))
                               v₀-shifted-α
                               (subst (λ a' → El (B a')) (e a) v₀-shifted-α)
                shift2 = subst-filler (λ a' → El (B a')) (e a) v₀-shifted-α

                -- Invert `transp-⅀IdlD` to express `transport (cong El (sym ⅀IdlD)) w`
                -- as `v₀-shifted-α`. Strategy: build `w-eq : w ≡ transport (cong El
                -- (⅀IdlD 𝒰 D)) v₀-shifted-α` (via `retEq` on `w`, the `b₀≡α`
                -- shift on the canonical pair, then `sym (transp-⅀IdlD)`); compose
                -- with `transport⁻Transport`.
                v₀-shifted-α-via-w
                  : transport (cong El (sym (⅀IdlD 𝒰 D))) w ≡ v₀-shifted-α
                v₀-shifted-α-via-w =
                    cong (transport (cong El (sym (⅀IdlD 𝒰 D)))) w-eq
                  ∙ transport⁻Transport (cong El (⅀IdlD 𝒰 D)) v₀-shifted-α
                  where
                    pair-shift : Path (Σ-syntax (El 𝜏) (λ b → El (D b)))
                                      (b₀-of a w , v₀-of a w)
                                      (α , v₀-shifted-α)
                    pair-shift = ΣPathP (b₀≡α a w , shift1)

                    w-eq : w ≡ transport (cong El (⅀IdlD 𝒰 D)) v₀-shifted-α
                    w-eq = sym (retEq (⟦⅀⟧ 𝜏 D) w)
                         ∙ cong (invEq (⟦⅀⟧ 𝜏 D)) pair-shift
                         ∙ sym (transp-⅀IdlD {𝒰 = 𝒰} D v₀-shifted-α)

                -- Match `subst (e a) v₀-shifted-α` (the right end of `shift2`) to
                -- `transport (cong El (funExt⁻ B-shape≡B a)) w` (the right end of
                -- `eq-snd`) via `congFunct + substComposite` and the inversion above.
                shift3 : subst (λ a' → El (B a')) (e a) v₀-shifted-α
                       ≡ transport (cong El (funExt⁻ B-shape≡B a)) w
                shift3 =
                    sym ( cong (subst (λ a' → El (B a')) (e a)) v₀-shifted-α-via-w )
                  ∙ sym ( substComposite (λ X → X)
                                          (cong El (sym (⅀IdlD 𝒰 D)))
                                          (cong El (cong B (e a))) w )
                  ∙ sym ( cong (λ q → transport q w)
                               (congFunct El (sym (⅀IdlD 𝒰 D)) (cong B (e a))) )

                eq-snd : PathP (λ i → El (B (eq-fst i)))
                               (v₀-of a w)
                               (transport (cong El (funExt⁻ B-shape≡B a)) w)
                eq-snd = compPathP' {B = λ a' → El (B a')} shift1 shift2 ▷ shift3

            -- Pointwise on canonical pairs: `LHS-chain ∙ cong invEq pair-eq ∙ sym RHS-chain`.
            pointwise-on-pair : (a : El A) (w : El (B-shape a))
                              → transport (cong El lhs-path)
                                          (invEq (⟦⅀⟧ A B-shape) (a , w))
                              ≡ transport (cong El rhs-path)
                                          (invEq (⟦⅀⟧ A B-shape) (a , w))
            pointwise-on-pair a w =
                LHS-chain a w
              ∙ cong (invEq (⟦⅀⟧ A B)) (pair-eq a w)
              ∙ sym (RHS-chain a w)

            -- Pointwise on arbitrary `y` by reducing to canonical via `retEq`.
            pointwise : (y : El (⅀ A B-shape))
                      → transport (cong El lhs-path) y
                      ≡ transport (cong El rhs-path) y
            pointwise y =
                cong (transport (cong El lhs-path)) (sym (retEq (⟦⅀⟧ A B-shape) y))
              ∙ pointwise-on-pair (fst (equivFun (⟦⅀⟧ A B-shape) y))
                                  (snd (equivFun (⟦⅀⟧ A B-shape) y))
              ∙ cong (transport (cong El rhs-path)) (retEq (⟦⅀⟧ A B-shape) y)

            equivs-agree : pathToEquiv (cong El lhs-path)
                         ≡ pathToEquiv (cong El rhs-path)
            equivs-agree = equivEq (funExt pointwise)

        -- After applying `subst-cong-⅀-node` with `B-shape≡B`, the per-fibre
        -- result must equal `ts`. The per-fibre subst over funExt⁻ B-shape≡B a
        -- applied to `per-fibre a` reduces (via substComposite) to a chain that
        -- collapses by `lCancel (⅀IdlD …)` and `apd ts (e a)`.
        ts-correct : (λ a → subst (FreeOps {𝒰 = 𝒰} K) (funExt⁻ B-shape≡B a) (per-fibre a)) ≡ ts
        ts-correct = funExt (λ a → ts-correct-fn a)
          where
            ts-correct-fn : (a : El A)
                          → subst (FreeOps {𝒰 = 𝒰} K) (funExt⁻ B-shape≡B a) (per-fibre a)
                          ≡ ts a
            ts-correct-fn a =
              -- LHS = subst (sym ⅀IdlD ∙ cong B (e a)) (per-fibre a). Split via substComposite,
              -- cancel sym⅀IdlD ∘ ⅀IdlD inside `per-fibre a` (which itself is subst by ⅀IdlD),
              -- and finish with apd ts (e a).
                substComposite (FreeOps {𝒰 = 𝒰} K)
                                (sym (⅀IdlD 𝒰 (λ b → B-tp (paired1 a b))))
                                (cong B (e a))
                                (per-fibre a)
              ∙ cong (subst (FreeOps {𝒰 = 𝒰} K) (cong B (e a)))
                     (cancel-⅀IdlD a)
              ∙ fromPathP {A = λ i → FreeOps {𝒰 = 𝒰} K (B (e a i))} (λ i → ts (e a i))
              where
                -- sym ⅀IdlD then ⅀IdlD substs cancel to refl-subst, recovering ts at paired1 α.
                cancel-⅀IdlD : (a : El A)
                             → subst (FreeOps {𝒰 = 𝒰} K)
                                     (sym (⅀IdlD 𝒰 (λ b → B-tp (paired1 a b))))
                                     (per-fibre a)
                             ≡ ts (transport (cong El p) (paired1 a α))
                cancel-⅀IdlD a' =
                    sym (substComposite (FreeOps {𝒰 = 𝒰} K)
                                         (⅀IdlD 𝒰 (λ b → B-tp (paired1 a' b)))
                                         (sym (⅀IdlD 𝒰 (λ b → B-tp (paired1 a' b))))
                                         (ts (transport (cong El p) (paired1 a' α))))
                  ∙ cong (λ pp → subst (FreeOps {𝒰 = 𝒰} K) pp
                                       (ts (transport (cong El p) (paired1 a' α))))
                         (rCancel (⅀IdlD 𝒰 (λ b → B-tp (paired1 a' b))))
                  ∙ substRefl {B = FreeOps {𝒰 = 𝒰} K}
                              (ts (transport (cong El p) (paired1 a' α)))

  module _ {L : Code → Type ℓl} (O : Operad 𝒰 L)
           (f : (A : Code) → K A → L A) where

    private
      id-O    = Operad.id O
      comp-O  = Operad.compₒ O
      isSet-L = Operad.isSetK O
      idl-O   = Operad.idl O
      idr-O   = Operad.idr O
      assoc-O = Operad.assoc O

    -- ==========================================================================
    -- §3  Underlying map `interp` (direct pattern-match)
    -- ==========================================================================
    interp : (A : Code) → FreeOps {𝒰 = 𝒰} K A → L A
    interp _ leaf                = id-O
    interp _ (node A B k ts)     = comp-O A B (f A k) (λ a → interp (B a) (ts a))
    interp A (set _ x y p q i j) =
      isSet-L A (interp A x) (interp A y)
                (λ k → interp A (p k))
                (λ k → interp A (q k)) i j

    -- ==========================================================================
    -- §4  `interp-subst` — naturality of `interp` w.r.t. `subst`.
    --
    -- A one-line invocation of `Cubical.Foundations.Transport.substCommSlice`,
    -- which gives `subst C p (F x u) ≡ F y (subst B p u)` for any `F : ∀ a → B a → C a`.
    -- ==========================================================================
    interp-subst : {A A' : Code} (p : A ≡ A') (x : FreeOps K A)
                 → interp A' (subst (FreeOps {𝒰 = 𝒰} K) p x) ≡ subst L p (interp A x)
    interp-subst p x = sym (substCommSlice (FreeOps K) L interp p x)

    -- ==========================================================================
    -- §5  `interp-graft` — interpretation commutes with grafting.
    --
    -- This is the `on-comp` field of the operad morphism `interpret`. Three
    -- cases mirroring `graft-idl/idr/assoc`.
    -- ==========================================================================

    -- §5a  Leaf case (A = 𝜏).
    --
    -- `graft 𝜏 B leaf ts = subst (FreeOps {𝒰 = 𝒰} K) (⅀IdlD 𝒰 B) (ts α)` where
    -- `α = invEq ⟦𝜏⟧ tt`. Pushing `interp` through the subst gives
    -- `subst L (⅀IdlD 𝒰 B) (interp (B α) (ts α))`. We then split `⅀IdlD 𝒰 B`
    -- into `sym (Inj (⅀Idl≃ (B α))) ∙ cong (⅀ 𝜏) B-const`, use `symP idl-O`
    -- to handle the first leg, and a PathP-based "family reindex" to handle
    -- the second.
    interp-graft-leaf : (B : El 𝜏 → Code)
                        (ts : (a : El 𝜏) → FreeOps {𝒰 = 𝒰} K (B a))
                      → interp (⅀ 𝜏 B) (graft {𝒰 = 𝒰} K 𝜏 B leaf ts)
                      ≡ comp-O 𝜏 B id-O (λ a → interp (B a) (ts a))
    interp-graft-leaf B ts =
        interp-subst (⅀IdlD 𝒰 B) (ts α)
      ∙ substComposite L (sym (Inj (⅀Idl≃ (B α))))
                         (cong (⅀ 𝜏) B-const)
                         (interp (B α) (ts α))
      ∙ cong (subst L (cong (⅀ 𝜏) B-const)) idl-step
      ∙ fromPathP comp-PathP
      where
        α : El 𝜏
        α = invEq ⟦𝜏⟧ tt

        B-const : (λ (_ : El 𝜏) → B α) ≡ B
        B-const = funExt (λ e → cong B (retEq ⟦𝜏⟧ e))

        -- `symP (idl-O …)` flipped to a `subst`-equation.
        idl-step : subst L (sym (Inj (⅀Idl≃ (B α)))) (interp (B α) (ts α))
                 ≡ comp-O 𝜏 (λ _ → B α) id-O (λ _ → interp (B α) (ts α))
        idl-step = fromPathP (symP (idl-O (B α) (interp (B α) (ts α))))

        -- Per-fibre PathP from `ts α` to `ts a`, lying over `B (retEq ⟦𝜏⟧ a i)`
        -- which is definitionally `B-const i a` (since funExt then-eval reduces).
        ts-PathP : (a : El 𝜏) → PathP (λ i → FreeOps K (B-const i a)) (ts α) (ts a)
        ts-PathP a i = ts (retEq ⟦𝜏⟧ a i)

        -- "Family reindex" PathP: at i=0 we have the constant-family comp-O;
        -- at i=1 we have the real comp-O at B. Glued by varying both the
        -- codomain family along `B-const` and the per-fibre values along
        -- `ts-PathP`.
        comp-PathP : PathP (λ i → L (⅀ 𝜏 (B-const i)))
                           (comp-O 𝜏 (λ _ → B α) id-O (λ _ → interp (B α) (ts α)))
                           (comp-O 𝜏 B id-O (λ a → interp (B a) (ts a)))
        comp-PathP i = comp-O 𝜏 (B-const i) id-O
                              (λ a → interp (B-const i a) (ts-PathP a i))

    -- §5b  Node case.
    --
    -- `graft (⅀ A' B') B (node A' B' k₀ ts') tss` is a subst over `⅀AssocD`
    -- of a `node` whose per-fibre subtrees are themselves grafts. We push
    -- `interp` inward via `interp-subst`, apply the inductive hypothesis on
    -- each fibre, then split `⅀AssocD = Inj (⅀Assoc≃ … C') ∙ cong (⅀ _) C'-eq`
    -- and discharge each leg by `assoc-O` and a "family-reindex" PathP.
    interp-graft : (A : Code) (B : El A → Code)
                   (t : FreeOps {𝒰 = 𝒰} K A) (ts : (a : El A) → FreeOps K (B a))
                 → interp (⅀ A B) (graft K A B t ts)
                 ≡ comp-O A B (interp A t) (λ a → interp (B a) (ts a))
    interp-graft _ B leaf ts = interp-graft-leaf B ts
    interp-graft _ B (node A' B' k₀ ts') tss =
        interp-subst (⅀AssocD 𝒰 A' B' B) inner-node
      ∙ cong (subst L (⅀AssocD 𝒰 A' B' B)) IH-applied
      ∙ substComposite L (Inj (⅀Assoc≃ A' B' C'))
                         (cong (⅀ (⅀ A' B')) C'-eq)
                         inner-LHS
      ∙ cong (subst L (cong (⅀ (⅀ A' B')) C'-eq)) assoc-step
      ∙ fromPathP final-PathP
      where
        paired : (a : El A') → El (B' a) → El (⅀ A' B')
        paired a b = invEq (⟦⅀⟧ A' B') (a , b)

        C' : (a : El A') → El (B' a) → Code
        C' a b = B (paired a b)

        C'-eq : ⅀Assoc-C' A' B' C' ≡ B
        C'-eq = funExt (λ x → cong B (retEq (⟦⅀⟧ A' B') x))

        -- Per-fibre grafted subtree, the argument to interp inside `inner-node`.
        graft-fib : (a' : El A') → FreeOps K (⅀ (B' a') (C' a'))
        graft-fib a' = graft K (B' a') (C' a') (ts' a') (λ b' → tss (paired a' b'))

        -- The body of the substed `node` in graft's node clause.
        inner-node : FreeOps K (⅀ A' (λ a' → ⅀ (B' a') (C' a')))
        inner-node = node A' (λ a' → ⅀ (B' a') (C' a')) k₀ graft-fib

        -- After interp on the node, with the inductive hypothesis applied
        -- at each fibre.
        inner-LHS : L (⅀ A' (λ a' → ⅀ (B' a') (C' a')))
        inner-LHS = comp-O A' (λ a' → ⅀ (B' a') (C' a')) (f A' k₀)
                          (λ a' → comp-O (B' a') (C' a') (interp (B' a') (ts' a'))
                                          (λ b' → interp (C' a' b') (tss (paired a' b'))))

        -- Apply the inductive hypothesis at each fibre via funExt + cong.
        IH-applied : comp-O A' (λ a' → ⅀ (B' a') (C' a')) (f A' k₀)
                            (λ a' → interp (⅀ (B' a') (C' a')) (graft-fib a'))
                   ≡ inner-LHS
        IH-applied = cong (comp-O A' (λ a' → ⅀ (B' a') (C' a')) (f A' k₀))
                          (funExt (λ a' → interp-graft (B' a') (C' a') (ts' a')
                                                        (λ b' → tss (paired a' b'))))

        -- `fromPathP assoc-O` flattens the heterogeneous associativity into a
        -- subst equation along `Inj (⅀Assoc≃ A' B' C')`.
        assoc-step : subst L (Inj (⅀Assoc≃ A' B' C')) inner-LHS
                   ≡ comp-O (⅀ A' B') (⅀Assoc-C' A' B' C')
                            (comp-O A' B' (f A' k₀) (λ a' → interp (B' a') (ts' a')))
                            (λ ab → interp (⅀Assoc-C' A' B' C' ab)
                                            (tss (paired (fst (equivFun (⟦⅀⟧ A' B') ab))
                                                          (snd (equivFun (⟦⅀⟧ A' B') ab)))))
        assoc-step = fromPathP
          (assoc-O A' B' C' (f A' k₀)
                            (λ a' → interp (B' a') (ts' a'))
                            (λ a' b' → interp (C' a' b') (tss (paired a' b'))))

        -- Per-fibre PathP varying `tss` along `retEq (⟦⅀⟧ A' B')`; the index
        -- type `λ i → FreeOps K (C'-eq i ab)` is definitionally
        -- `λ i → FreeOps K (B (retEq ⟦⅀⟧ ab i))` (funExt-then-eval).
        tss-PathP : (ab : El (⅀ A' B'))
                  → PathP (λ i → FreeOps K (C'-eq i ab))
                          (tss (paired (fst (equivFun (⟦⅀⟧ A' B') ab))
                                        (snd (equivFun (⟦⅀⟧ A' B') ab))))
                          (tss ab)
        tss-PathP ab i = tss (retEq (⟦⅀⟧ A' B') ab i)

        -- "Family reindex" PathP closing the gap between `⅀Assoc-C' A' B' C'`
        -- and `B`, varying both the codomain family along `C'-eq` and the
        -- per-fibre `tss`-values along `tss-PathP`.
        final-PathP : PathP (λ i → L (⅀ (⅀ A' B') (C'-eq i)))
                            (comp-O (⅀ A' B') (⅀Assoc-C' A' B' C')
                                    (comp-O A' B' (f A' k₀) (λ a' → interp (B' a') (ts' a')))
                                    (λ ab → interp (⅀Assoc-C' A' B' C' ab)
                                                    (tss (paired (fst (equivFun (⟦⅀⟧ A' B') ab))
                                                                  (snd (equivFun (⟦⅀⟧ A' B') ab))))))
                            (comp-O (⅀ A' B') B
                                    (comp-O A' B' (f A' k₀) (λ a' → interp (B' a') (ts' a')))
                                    (λ ab → interp (B ab) (tss ab)))
        final-PathP i = comp-O (⅀ A' B') (C'-eq i)
                              (comp-O A' B' (f A' k₀) (λ a' → interp (B' a') (ts' a')))
                              (λ ab → interp (C'-eq i ab) (tss-PathP ab i))

    -- §5c  Set case — prop fill in the h-set `L (⅀ A B)`.
    --
    -- The goal at each (i, j) is a path in `L (⅀ A B)` — a proposition since
    -- `L (⅀ A B)` is a set. The square is filled by `isProp→SquareP` from the
    -- four recursive calls of `interp-graft` on the cell's faces.
    interp-graft A B (set _ x y p q i j) ts =
      isProp→SquareP
        {B = λ i' j' → interp (⅀ A B) (graft K A B (set A x y p q i' j') ts)
                     ≡ comp-O A B (interp A (set A x y p q i' j'))
                                  (λ a → interp (B a) (ts a))}
        (λ _ _ → isSet-L (⅀ A B) _ _)
        (λ _  → interp-graft A B x ts)
        (λ _  → interp-graft A B y ts)
        (λ jj → interp-graft A B (p jj) ts)
        (λ jj → interp-graft A B (q jj) ts)
        i j

    -- ==========================================================================
    -- §6  `interpret` — the operad morphism.
    -- ==========================================================================
    interpret : FreeOperad {𝒰 = 𝒰} K ⇒ O
    _⇒_.⟪_⟫    interpret             = interp
    _⇒_.on-id  interpret             = refl
    _⇒_.on-comp interpret A B k₀ ts  = interp-graft A B k₀ ts

    -- ==========================================================================
    -- §7  η-correctness — `interp` recovers `f` along `η`.
    --
    -- η A k = subst FreeOps (Inj (⅀Idr≃ A)) (node A (λ _ → 𝜏) k (λ _ → leaf)).
    -- Pushing `interp` through the subst (by `interp-subst`) and reducing on
    -- the node (interp's node clause gives `comp-O A (λ _ → 𝜏) (f A k) (λ _ → id-O)`),
    -- the right-unitor `idr-O A (f A k)` flips the subst to refl.
    -- ==========================================================================
    η-correct : (A : Code) (k : K A) → interp A (η A k) ≡ f A k
    η-correct A k =
        interp-subst (Inj (⅀Idr≃ A)) (node A (λ _ → 𝜏) k (λ _ → leaf))
      ∙ fromPathP (idr-O A (f A k))

    -- ==========================================================================
    -- §8  Uniqueness: any morphism g satisfying `g η = f` equals `interpret`.
    --
    -- By induction on `t : FreeOps K A` we show `⟪g⟫ A t ≡ interp A t`.
    --   * leaf: `⟪g⟫ 𝜏 leaf = id-O = interp 𝜏 leaf` by `on-id g`.
    --   * node: rewrite `node A B k ts = graft A B (η A k) ts` (via `graft-eta`),
    --     then `on-comp g` distributes ⟪g⟫ over graft, then `g-on-η` and the
    --     inductive hypothesis on children close the equation.
    --   * set:  the equation lives in the h-set `L A`; `isProp→SquareP` fills.
    -- ==========================================================================
    agree : (g : FreeOperad {𝒰 = 𝒰} K ⇒ O)
          → ((A : Code) (k : K A) → _⇒_.⟪_⟫ g A (η A k) ≡ f A k)
          → (A : Code) (t : FreeOps {𝒰 = 𝒰} K A) → _⇒_.⟪_⟫ g A t ≡ interp A t
    agree g g-on-η _ leaf = _⇒_.on-id g
    agree g g-on-η _ (node A B k₀ ts) =
        cong (_⇒_.⟪_⟫ g (⅀ A B)) (sym (graft-eta A B k₀ ts))
      ∙ _⇒_.on-comp g A B (η A k₀) ts
      ∙ cong₂ (comp-O A B)
              (g-on-η A k₀)
              (funExt (λ a → agree g g-on-η (B a) (ts a)))
    agree g g-on-η A (set _ x y p q i j) =
      isProp→SquareP
        {B = λ i' j' → _⇒_.⟪_⟫ g A (set A x y p q i' j') ≡ interp A (set A x y p q i' j')}
        (λ _ _ → isSet-L A _ _)
        (λ _  → agree g g-on-η A x)
        (λ _  → agree g g-on-η A y)
        (λ jj → agree g g-on-η A (p jj))
        (λ jj → agree g g-on-η A (q jj))
        i j

    -- A morphism `g` extending `f` along `η` equals `interpret O f` as functions.
    agree-funExt : (g : FreeOperad {𝒰 = 𝒰} K ⇒ O)
                 → ((A : Code) (k : K A) → _⇒_.⟪_⟫ g A (η A k) ≡ f A k)
                 → (λ A t → _⇒_.⟪_⟫ g A t) ≡ (λ A t → interp A t)
    agree-funExt g g-on-η = funExt (λ A → funExt (agree g g-on-η A))

    -- Σ-extensionality for operad morphisms: two morphisms with equal
    -- underlying maps are equal. The `on-id` and `on-comp` fields are
    -- propositions (paths in the h-set `L _`), so they auto-cohere.
    morphism-≡ : (g h : FreeOperad {𝒰 = 𝒰} K ⇒ O)
               → ((A : Code) (t : FreeOps {𝒰 = 𝒰} K A) → _⇒_.⟪_⟫ g A t ≡ _⇒_.⟪_⟫ h A t)
               → g ≡ h
    _⇒_.⟪_⟫     (morphism-≡ g h eq i) A t = eq A t i
    _⇒_.on-id   (morphism-≡ g h eq i) =
      isProp→PathP (λ i' → isSet-L 𝜏 (eq 𝜏 leaf i') id-O)
                    (_⇒_.on-id g) (_⇒_.on-id h) i
    _⇒_.on-comp (morphism-≡ g h eq i) A B k₀ ts =
      isProp→PathP (λ i' → isSet-L (⅀ A B) (eq (⅀ A B) (graft K A B k₀ ts) i')
                                            (comp-O A B (eq A k₀ i')
                                                        (λ a → eq (B a) (ts a) i')))
                    (_⇒_.on-comp g A B k₀ ts)
                    (_⇒_.on-comp h A B k₀ ts) i

    -- ==========================================================================
    -- §9  Universal property — contractibility of the factorisation type.
    --
    -- This `isContr` statement is the *categorical* universal property of the
    -- free operad: for any operad `O` on `L` and any species morphism
    -- `f : ∀ A → K A → L A`, the factorisation `(g, g ∘ η ≡ f)` is unique
    -- up to (proof-irrelevant) propositional equality. Equivalently,
    -- `(FreeOperad K ⇒ O)` is naturally equivalent to species morphisms
    -- `K → U(O)`, exhibiting `FreeOperad` as left adjoint to the forgetful
    -- functor `U` from 𝒰-operads to 𝒰-species.
    -- ==========================================================================
    universal : isContr (Σ[ g ∈ (FreeOperad {𝒰 = 𝒰} K ⇒ O) ]
                          ((A : Code) (k : K A) → _⇒_.⟪_⟫ g A (η A k) ≡ f A k))
    fst universal = interpret , η-correct
    snd universal (g , g-on-η) =
      ΣPathP ( morphism-≡ interpret g (λ A t → sym (agree g g-on-η A t))
             , isProp→PathP
                  (λ i → isPropΠ2
                            (λ A k → isSet-L A
                                       (_⇒_.⟪_⟫ (morphism-≡ interpret g
                                                  (λ A' t → sym (agree g g-on-η A' t)) i)
                                                A (η A k))
                                       (f A k)))
                  η-correct g-on-η )
