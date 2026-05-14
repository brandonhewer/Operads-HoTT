{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Free.IR.FiberEquiv
--
-- The constructive fiberwise equivalence
--
--     FreeOps {𝒰 = 𝒰} K A  ≃  Fiber {𝒰 = 𝒰} K A   (= Σ[ t ∈ FreeOpsIR {𝒰 = 𝒰} K ] CodeOp {𝒰 = 𝒰} K t ≡ A)
--
-- between the indexed HIT presentation of the free operad and the
-- Σ-fibred presentation built on the IR data type. The operad structure
-- itself on `FreeOps' K = Fiber K` is assembled in `HoTTOperads.Free.IR`
-- using a direct IR `graft` together with operad laws derived (by transport
-- along this equivalence) from `HoTTOperads.Free.HIT`.
-- ============================================================================
module HoTTOperads.Free.IR.FiberEquiv where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Free.IR.Base
open import HoTTOperads.Free.HIT renaming (FreeOperad to FreeOperadHIT)

private
  variable
    ℓc ℓe ℓk : Level

module _ {𝒰 : Universe ℓc ℓe} (K : Universe.Code 𝒰 → Type ℓk) where
  open Universe 𝒰

  -- ============================================================================
  -- §1  HIT → Fiber
  --
  -- Maps each `FreeOps {𝒰 = 𝒰} K A` constructor to its IR counterpart, packaged
  -- together with the path identifying its CodeOp with the original index.
  -- At the `set` constructor we use `isSetFiberCodeOp` from `Free.IR.Base` to fill
  -- the 2-cell.
  -- ============================================================================
  to : (A : Code) → FreeOps {𝒰 = 𝒰} K A → Fiber {𝒰 = 𝒰} K A
  to _ leaf = (leaf , refl)
  to _ (node A B k ts) =
    ( node A k (λ a → fst (to (B a) (ts a)))
    , cong (⅀ A) (funExt (λ a → snd (to (B a) (ts a))))
    )
  to A (set _ x y p q i j) =
    isSetFiberCodeOp {𝒰 = 𝒰} K A (to A x) (to A y) (cong (to A) p) (cong (to A) q) i j

  -- ============================================================================
  -- §2  IR-level forgetful map and Fiber → HIT
  --
  -- `g t` exhibits each `t : FreeOpsIR` as an element of `FreeOps {𝒰 = 𝒰} K (CodeOp t)`.
  -- The `set` constructor case is filled by `isSet→SquareP` on the HIT's `set`
  -- constructor; the boundary check uses the IR clause
  -- `CodeOp (set … i j) = s j i`.
  -- ============================================================================
  g : (t : FreeOpsIR {𝒰 = 𝒰} K) → FreeOps {𝒰 = 𝒰} K (CodeOp {𝒰 = 𝒰} K t)
  g leaf            = leaf
  g (node A k ts)   = node A (λ a → CodeOp {𝒰 = 𝒰} K (ts a)) k (λ a → g (ts a))
  g (set t u p q s i j) =
    isSet→SquareP
      {A = λ i' j' → FreeOps {𝒰 = 𝒰} K (s j' i')}
      (λ i' j' → set (s j' i'))
      (λ j' → g (p j'))
      (λ j' → g (q j'))
      (λ _ → g t)
      (λ _ → g u)
      i j

  from : (A : Code) → Fiber {𝒰 = 𝒰} K A → FreeOps {𝒰 = 𝒰} K A
  from A (t , p) = subst (FreeOps {𝒰 = 𝒰} K) p (g t)

  -- ============================================================================
  -- §3  Section: `to ∘ from ≡ id`
  --
  -- Reduces along the path component `p : CodeOp t ≡ A` to the base case
  -- `p ≡ refl`, where the goal collapses to `to (CodeOp t) (g t) ≡ (t , refl)`.
  -- That lemma is proved inductively on `t` — for `node` the Σ-path is given
  -- as a direct cubical filler whose i = 1 endpoint reduces definitionally to
  -- `(node A k ts , refl)`; for the IR `set` we fill via `isSet→SquareP` on
  -- `isSetFiberCodeOp`.
  -- ============================================================================
  g-to-section : (t : FreeOpsIR {𝒰 = 𝒰} K) → to (CodeOp {𝒰 = 𝒰} K t) (g t) ≡ (t , refl)
  g-to-section leaf            = refl
  g-to-section (node A k ts) i =
    ( node A k (λ a → fst (g-to-section (ts a) i))
    , (λ j → ⅀ A (λ a → snd (g-to-section (ts a) i) j))
    )
  g-to-section (set t u p q s i j) =
    isSet→SquareP
      {A = λ i' j' →
        to (CodeOp {𝒰 = 𝒰} K (set t u p q s i' j')) (g (set t u p q s i' j'))
        ≡ (set t u p q s i' j' , refl)}
      (λ _ _ → isProp→isSet (isSetFiberCodeOp {𝒰 = 𝒰} K _ _ _))
      (λ j' → g-to-section (p j'))
      (λ j' → g-to-section (q j'))
      (λ _ → g-to-section t)
      (λ _ → g-to-section u)
      i j

  section : (A : Code) (q : Fiber {𝒰 = 𝒰} K A) → to A (from A q) ≡ q
  section A (t , p) =
    J (λ A' p' → to A' (subst (FreeOps {𝒰 = 𝒰} K) p' (g t)) ≡ (t , p'))
      (cong (to (CodeOp {𝒰 = 𝒰} K t)) (substRefl {B = FreeOps {𝒰 = 𝒰} K} (g t))
         ∙ g-to-section t)
      p

  -- ============================================================================
  -- §4  Retract: `from ∘ to ≡ id`
  --
  -- Direct HIT induction. The `node` case rewrites the outer `subst (FreeOps {𝒰 = 𝒰} K)
  -- (cong (⅀ A) (funExt …))` through `subst-cong-⅀-node` (from
  -- `HoTTOperads.Free.HIT`), at which point `funExt⁻ (funExt f) a ≡ f a`
  -- reduces definitionally and the pointwise IH closes the goal. The HIT `set`
  -- constructor case is filled by `isSet→SquareP` on the fact that paths in a
  -- set form a prop.
  -- ============================================================================
  retract : (A : Code) (x : FreeOps {𝒰 = 𝒰} K A) → from A (to A x) ≡ x
  retract _ leaf = substRefl {B = FreeOps {𝒰 = 𝒰} K} leaf
  retract _ (node A B k ts) = step₁ ∙ step₂
    where
      ir-tree : (a : El A) → FreeOpsIR {𝒰 = 𝒰} K
      ir-tree a = fst (to (B a) (ts a))
      ir-path : (a : El A) → CodeOp {𝒰 = 𝒰} K (ir-tree a) ≡ B a
      ir-path a = snd (to (B a) (ts a))
      step₁ : subst (FreeOps {𝒰 = 𝒰} K) (cong (⅀ A) (funExt ir-path))
                    (node A (λ a → CodeOp {𝒰 = 𝒰} K (ir-tree a)) k (λ a → g (ir-tree a)))
            ≡ node {𝒰 = 𝒰} {K = K} A B k
                   (λ a → subst (FreeOps {𝒰 = 𝒰} K) (ir-path a) (g (ir-tree a)))
      step₁ = subst-cong-⅀-node {𝒰 = 𝒰} K A (funExt ir-path) k (λ a → g (ir-tree a))
      step₂ : node {𝒰 = 𝒰} {K = K} A B k
                   (λ a → subst (FreeOps {𝒰 = 𝒰} K) (ir-path a) (g (ir-tree a)))
            ≡ node {𝒰 = 𝒰} {K = K} A B k ts
      step₂ i = node {𝒰 = 𝒰} {K = K} A B k
                     (λ a → retract (B a) (ts a) i)
  retract A (set _ x y p q i j) =
    isSet→SquareP
      {A = λ i' j' →
        from A (to A (set {𝒰 = 𝒰} {K = K} A x y p q i' j'))
        ≡ set {𝒰 = 𝒰} {K = K} A x y p q i' j'}
      (λ _ _ → isProp→isSet (set {𝒰 = 𝒰} {K = K} A _ _))
      (λ k → retract A (p k))
      (λ k → retract A (q k))
      (λ _ → retract A x)
      (λ _ → retract A y)
      i j

  -- ============================================================================
  -- §5  Assembled equivalence
  -- ============================================================================
  FreeOps≃Fiber : (A : Code) → FreeOps {𝒰 = 𝒰} K A ≃ Fiber {𝒰 = 𝒰} K A
  FreeOps≃Fiber A = isoToEquiv (iso (to A) (from A) (section A) (retract A))

  FreeOps≡FreeOps' : FreeOps {𝒰 = 𝒰} K ≡ FreeOps' {𝒰 = 𝒰} K
  FreeOps≡FreeOps' i A = ua (FreeOps≃Fiber A) i
