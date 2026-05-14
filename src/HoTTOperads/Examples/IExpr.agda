{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Examples.IExpr
--
-- The NonSymmOperad on the inductive family `IExpr : ℕ → Type`, whose
-- operations are the abstract syntax of a tiny arithmetic-expression
-- language. We follow BasicIdea.tex §1: `id↑` is the unit at arity 1,
-- `val↑ n` an arity-0 value constant, and `add↑ e₁ e₂` an arity-`(m + n)`
-- node built from `e₁ : IExpr m` and `e₂ : IExpr n`. Operadic composition
-- `IExpr-comp` is defined by induction on the IExpr argument; the three
-- coherence laws (left identity, right identity, associativity) are
-- discharged constructively in Cubical Agda.
--
-- ## File layout
--
--   §1  Tree (free unindexed witness type) and `isSetTree` via
--       encode-decode.
--   §2  Shape, forget, canonical (the retract pair from `IExpr n` into
--       `Σ[ t ∈ Tree ] (shape t ≡ n)`) and `subst-add↑`.
--   §3  `isSetIExpr` by retract.
--   §4  `IExpr-comp` (the operadic composition).
--   §5  `IExpr-idl` (left identity).
--   §6  `IExpr-idr` (right identity).
--   §7  Joint-form toolkit for the add↑ case
--         `joint-C'`, `joint-kss`, `joint-C'-on-inj{L,R}`,
--         `joint-kss-on-inj{L,R}`.
--   §8  PathP toolkit for the (m+n)-Fubini side of assoc
--         `B-path-add↑(-pointwise)`, `es-path-add↑(-pointwise)`,
--         `IExpr-comp-add↑-lemma`.
--   §9  `IExpr-assoc-id↑` (assoc, A = 1 case) — assembled from
--         `Xinner-id↑`, `lhs-id↑`, `rhs-id↑`, `bridge-id↑`, `outer-id↑`,
--         `chosen-path-id↑`, `my-PathP-id↑`.
--   §10 `IExpr-assoc-add↑` (assoc, A = m+n case) — the step A→B→C→D
--         decomposition.
--   §11 `IExpr-assoc` (top-level dispatch).
--   §12 `IExprOperad` (record assembly).
--
-- ## The recurring patterns ("recipes")
--
-- The associativity proof is structured around four reusable patterns;
-- each appears at several sites and is named here so call sites stay short.
--
--   (a) **subst-filler reversal** — `symP (subst-filler IExpr p x)` gives a
--       PathP from `subst IExpr p x` to `x` over `p`. We use this every
--       time `IExpr-comp` reduces to a `subst` on the canonical normal
--       form, and we need a heterogeneous bridge back. Sites: `outer-id↑`,
--       `step-A-add↑`, `IExpr-comp-add↑-lemma`, `filler-path` in
--       `IExpr-idr`'s `add↑` case.
--
--   (b) **`IExpr-comp-PathP` cong** — `IExpr-comp` is structural in its
--       four arguments (arity, family, IExpr, dependent function), so we
--       have a generic PathP-cong over all four. Sites: `bridge-id↑`,
--       `step-C-add↑`, `step-D-add↑`.
--
--   (c) **`isSetℕ` swap** — `isSet→subst-PathP isSetℕ` turns a structural
--       ℕ-index path into the desired `Inj 𝓝 (⅀Idl≃ A)` /
--       `Inj 𝓝 (⅀Idr≃ A)` / `Inj 𝓝 (⅀Assoc≃ A B C)` index path. ℕ being a
--       set, the swap is essentially free. Sites: every endpoint-PathP
--       to final-PathP step.
--
--   (d) **joint-form bridge (§7)** — case-split a function on
--       `Fin (sum m … + sum n …)` via `_≤?_`, prove its restriction to
--       `inj-l-+` equals the m-side form and its restriction to
--       `inj-r-+` equals the n-side form.
--
--   (e) **step A→B→C→D (§10)** — the four-leg `compPathP'` decomposition
--       of `IExpr-assoc-add↑`: A is subst-filler reversal (LHS to
--       `add↑`), B is cong-`add↑` on the per-fibre IHs, C is the
--       joint-form bridge into the joint domain, D is `IExpr-comp-PathP`
--       through the (m+n)-Fubini path.
--
-- ## Opacity conventions
--
-- Path-valued lemmas are `opaque`. `unfolding` lists are minimal — never
-- wider than the definitional reductions needed at the call site. The
-- four IH-endpoint definitions of §10 (`Xinner-L/R-add↑`,
-- `recL/R-IHend-add↑`) are `opaque` *and* unfolded in `IExpr-assoc`'s
-- final clause so the subst's motive matches the declared return type
-- by name. Several `where`-bound path-valued helpers inside long
-- `let`-blocks are themselves wrapped in `opaque` to seal one-shot
-- normalisations; proof-of-`<` propositions are kept transparent since
-- `isProp≤`/`isProp→PathP` already black-box them.
-- ============================================================================
module HoTTOperads.Examples.IExpr where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties using (+-zero ; +-assoc ; +-comm)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; ¬-<-zero
                                          ; isProp≤ ; <-weaken ; <-k+)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Fin.Properties using (Fin-fst-≡ ; _≤?_ ; ∸-<-lemma
                                              ; m+n∸n=m ; ∸-lemma ; isSetFin
                                              ; o<m→o<m+n)
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (Σ≡Prop ; ΣPathP)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Instances.Nat using
  ( 𝓝 ; sum ; ⅀Assoc-C'-on-inl ; ⅀Assoc-C'-on-inr
  ; ⅀Assoc-C'-add↑-on-l ; ⅀Assoc-C'-add↑-on-r )
open import HoTTOperads.Prelude.Nat using
  ( transport-Fin-fst ; sumFinFwd ; sum-prefix-bound
  ; absurd-≤? ; absurd-+-≤? ; inj-l-+ ; inj-r-+ ; sum-split
  ; sumFinFwd-suc-inl-fst ; sumFinFwd-suc-inl-snd
  ; sumFinFwd-suc-inr-fst ; sumFinFwd-suc-inr-snd
  ; sumFinFwd-add↑-on-l ; sumFinFwd-add↑-on-r )
open import HoTTOperads.Prelude.Path using (isSet→subst-PathP)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Specialised.NonSymm using (NonSymmOperad)

-- A simple expression language used as a worked target for the operad.
-- This module never inspects `Expr` itself; it's defined here as a
-- documentation reminder of what an `IExpr n` operationally represents.
data Expr : Type where
  val : ℕ → Expr
  add : Expr → Expr → Expr

-- The abstract operations as an inductive family indexed by arity. An
-- `IExpr n` is a syntactic operation with `n` named input slots:
--   `id↑`     — the singleton-input identity (slot count 1).
--   `val↑ k`  — the constant `val k` (slot count 0).
--   `add↑ e₁ e₂` — adds the values returned by `e₁` and `e₂`, with the
--                  combined input slots laid out left-to-right.
data IExpr : ℕ → Type where
  id↑  : IExpr 1
  val↑ : ℕ → IExpr 0
  add↑ : ∀ {m n} → IExpr m → IExpr n → IExpr (m + n)

-- ============================================================================
-- §1  Tree: an unindexed witness type for IExpr.
--
-- `Tree` is the free inductive type with the same shape as IExpr but
-- with `Tid`/`Tval k`/`Tadd l r` replacing the indexed `id↑`/`val↑ k`/
-- `add↑ e₁ e₂`. It serves as the target of a retract `IExpr n →
-- IExprTreeΣ n → IExpr n` (§2-§3) used to prove `isSetIExpr` from
-- `isSetTree`. `isSetTree` itself follows by the standard encode-decode
-- argument since `Tree` is a free inductive type.
-- ============================================================================
data Tree : Type where
  Tid  : Tree
  Tval : ℕ → Tree
  Tadd : Tree → Tree → Tree

-- Encode-decode at `Tree`. `Cover s t` is the *family of paths*
-- `s ≡ t` defined by recursion on the constructor pair: `Unit` at
-- matching nullary constructors, `m ≡ n` at matching `Tval`, the
-- product of subtree covers at matching `Tadd`, `⊥` otherwise. The
-- `encode`/`decode` round-trip is the usual `J`-driven construction;
-- the only h-level fact we need is that each `Cover` fibre is at most
-- one universe level above `isSetℕ` (proved structurally).
private
  module TreePath where
    Cover : Tree → Tree → Type
    Cover Tid          Tid          = Unit
    Cover Tid          (Tval _)     = ⊥
    Cover Tid          (Tadd _ _)   = ⊥
    Cover (Tval _)     Tid          = ⊥
    Cover (Tval m)     (Tval n)     = m ≡ n
    Cover (Tval _)     (Tadd _ _)   = ⊥
    Cover (Tadd _ _)   Tid          = ⊥
    Cover (Tadd _ _)   (Tval _)     = ⊥
    Cover (Tadd l₁ r₁) (Tadd l₂ r₂) = Cover l₁ l₂ × Cover r₁ r₂

    opaque
      reflCode : (t : Tree) → Cover t t
      reflCode Tid         = tt
      reflCode (Tval _)    = refl
      reflCode (Tadd l r)  = reflCode l , reflCode r

      encode : (s t : Tree) → s ≡ t → Cover s t
      encode s _ = J (λ t _ → Cover s t) (reflCode s)

      encodeRefl : (s : Tree) → encode s s refl ≡ reflCode s
      encodeRefl s = JRefl (λ t _ → Cover s t) (reflCode s)

      decode : (s t : Tree) → Cover s t → s ≡ t
      decode Tid          Tid          _       = refl
      decode (Tval _)     (Tval _)     p       = cong Tval p
      decode (Tadd l₁ r₁) (Tadd l₂ r₂) (cl , cr) =
        cong₂ Tadd (decode l₁ l₂ cl) (decode r₁ r₂ cr)

      decodeRefl : (s : Tree) → decode s s (reflCode s) ≡ refl
      decodeRefl Tid        = refl
      decodeRefl (Tval _)   = refl
      decodeRefl (Tadd l r) i = cong₂ Tadd (decodeRefl l i) (decodeRefl r i)

      decodeEncode : (s t : Tree) (p : s ≡ t) → decode s t (encode s t p) ≡ p
      decodeEncode s _ = J (λ t p → decode s t (encode s t p) ≡ p)
                           (cong (decode s s) (encodeRefl s) ∙ decodeRefl s)

      isOfHLevelCover : (n : HLevel) → ∀ s t → isOfHLevel (suc n) (Cover s t)
      isOfHLevelCover n Tid          Tid          =
        isProp→isOfHLevelSuc n isPropUnit
      isOfHLevelCover n Tid          (Tval _)     =
        isProp→isOfHLevelSuc n (λ x → ⊥-rec x)
      isOfHLevelCover n Tid          (Tadd _ _)   =
        isProp→isOfHLevelSuc n (λ x → ⊥-rec x)
      isOfHLevelCover n (Tval _)     Tid          =
        isProp→isOfHLevelSuc n (λ x → ⊥-rec x)
      isOfHLevelCover n (Tval m)     (Tval m')    =
        isProp→isOfHLevelSuc n (isSetℕ m m')
      isOfHLevelCover n (Tval _)     (Tadd _ _)   =
        isProp→isOfHLevelSuc n (λ x → ⊥-rec x)
      isOfHLevelCover n (Tadd _ _)   Tid          =
        isProp→isOfHLevelSuc n (λ x → ⊥-rec x)
      isOfHLevelCover n (Tadd _ _)   (Tval _)     =
        isProp→isOfHLevelSuc n (λ x → ⊥-rec x)
      isOfHLevelCover n (Tadd l₁ r₁) (Tadd l₂ r₂) =
        isOfHLevelΣ (suc n) (isOfHLevelCover n l₁ l₂)
                            (λ _ → isOfHLevelCover n r₁ r₂)

-- `isSetTree` by retract: the path-space of `Tree` retracts onto `Cover`
-- (a Σ-of-prop-or-set), which is a set by induction.
opaque
  isSetTree : isSet Tree
  isSetTree s t =
    isOfHLevelRetract 1
      (TreePath.encode s t)
      (TreePath.decode s t)
      (TreePath.decodeEncode s t)
      (TreePath.isOfHLevelCover 0 s t)

-- ============================================================================
-- §2  Shape, forget, canonical: the retract pair `IExpr n ↔ IExprTreeΣ n`.
--
-- `forget` strips the arity index, `shape` recovers it from the tree.
-- `canonical` provides the section: every tree `t` carries a canonical
-- `IExpr (shape t)` lift. Together with `subst-add↑` (`subst IExpr`
-- distributes through `add↑`) these give the round-trip `g ∘ f ≡ id`
-- that drives `isSetIExpr` in §3.
-- ============================================================================
shape : Tree → ℕ
shape Tid          = 1
shape (Tval _)     = 0
shape (Tadd t₁ t₂) = shape t₁ + shape t₂

forget : ∀ {n} → IExpr n → Tree
forget id↑          = Tid
forget (val↑ n)     = Tval n
forget (add↑ e₁ e₂) = Tadd (forget e₁) (forget e₂)

shape-correct : ∀ {n} (e : IExpr n) → shape (forget e) ≡ n
shape-correct id↑          = refl
shape-correct (val↑ _)     = refl
shape-correct (add↑ e₁ e₂) = cong₂ _+_ (shape-correct e₁) (shape-correct e₂)

canonical : (t : Tree) → IExpr (shape t)
canonical Tid          = id↑
canonical (Tval n)     = val↑ n
canonical (Tadd t₁ t₂) = add↑ (canonical t₁) (canonical t₂)

-- Pushing `subst IExpr` through an outer `add↑`. Mirrors
-- `SymExpr.subst-add↑`. Used in the `g ∘ f` round-trip below and in
-- `IExpr-idr`'s `add↑` case (§6). Proved by lifting the two
-- `subst-filler`s into a single PathP over `add↑`, then `fromPathP`.
opaque
  subst-add↑ : ∀ {m m' n n'}
               (p₁ : m ≡ m') (p₂ : n ≡ n')
               (e₁ : IExpr m) (e₂ : IExpr n)
             → subst IExpr (cong₂ _+_ p₁ p₂) (add↑ e₁ e₂)
             ≡ add↑ (subst IExpr p₁ e₁) (subst IExpr p₂ e₂)
  subst-add↑ p₁ p₂ e₁ e₂ =
    fromPathP (λ i → add↑ (subst-filler IExpr p₁ e₁ i)
                          (subst-filler IExpr p₂ e₂ i))

-- The retract pair `(f, g)` and the round-trip `g ∘ f ≡ id`. Mirrors
-- `SymExpr.f` / `SymExpr.g` / `SymExpr.g∘f` at the ℕ-indexed level.
-- `g∘f` is kept transparent: making it `opaque` breaks `substRefl`
-- family inference inside `isSetIExpr`.
IExprTreeΣ : ℕ → Type
IExprTreeΣ n = Σ[ t ∈ Tree ] (shape t ≡ n)

f : ∀ {n} → IExpr n → IExprTreeΣ n
f e = forget e , shape-correct e

g : ∀ {n} → IExprTreeΣ n → IExpr n
g (t , p) = subst IExpr p (canonical t)

g∘f : ∀ {n} (e : IExpr n) → g (f e) ≡ e
g∘f id↑          = substRefl {B = IExpr} id↑
g∘f (val↑ n)     = substRefl {B = IExpr} (val↑ n)
g∘f (add↑ e₁ e₂) =
    subst-add↑ (shape-correct e₁) (shape-correct e₂)
               (canonical (forget e₁)) (canonical (forget e₂))
  ∙ λ i → add↑ (g∘f e₁ i) (g∘f e₂ i)

-- ============================================================================
-- §3  `isSetIExpr` by retract to `IExprTreeΣ`.
--
-- `IExprTreeΣ n` is a Σ of a set (`Tree`) and a set (`ℕ`-paths), so it
-- is itself a set. Composing with the retract `(f, g, g∘f)` gives
-- `isSetIExpr`.
-- ============================================================================
opaque
  isSetIExprTreeΣ : (n : ℕ) → isSet (IExprTreeΣ n)
  isSetIExprTreeΣ n = isSetΣ isSetTree (λ t → isProp→isSet (isSetℕ (shape t) n))

  isSetIExpr : (n : ℕ) → isSet (IExpr n)
  isSetIExpr n = isOfHLevelRetract 2 f g g∘f (isSetIExprTreeΣ n)

------------------------------------------------------------------------
-- §4  IExpr-comp: the n-ary operadic composition.
--
-- Defined by induction on the IExpr argument (BasicIdea.tex §1):
--   * `id↑` at arity 1: the unique input is the result, transported
--     across `+-zero` to land in `Fin (B fzero + 0)`.
--   * `val↑ k` at arity 0: the result is `val↑ k` itself (no inputs).
--   * `add↑ e₁ e₂` at arity `m + n`: recurse on both halves and combine
--     with `add↑`, then `subst` across `sum-split` to bring the indices
--     into the operadic form.
--
-- `inj-l-+`, `inj-r-+`, and `sum-split` come from
-- `HoTTOperads.Prelude.Nat`; we don't redefine them here.
------------------------------------------------------------------------
IExpr-comp : (A : ℕ) (B : Fin A → ℕ)
           → IExpr A → ((a : Fin A) → IExpr (B a))
           → IExpr (sum A B)
IExpr-comp .1     B id↑                   es =
  subst IExpr (sym (+-zero (B fzero))) (es fzero)
IExpr-comp .0     B (val↑ k)              es =
  val↑ k
IExpr-comp .(m + n) B (add↑ {m} {n} e₁ e₂) es =
  subst IExpr (sym (sum-split m n B))
    (add↑ (IExpr-comp m (B ∘ inj-l-+ m n) e₁ (es ∘ inj-l-+ m n))
          (IExpr-comp n (B ∘ inj-r-+ m n) e₂ (es ∘ inj-r-+ m n)))

private
  opaque
    -- The "`IExpr-comp-PathP` cong" recipe (b). `IExpr-comp` is structural
    -- in all four of its arguments (arity, family, IExpr, dependent
    -- function), so a single PathP-cong handles every site that needs
    -- to vary `IExpr-comp` heterogeneously. Used in `bridge-id↑` (§9),
    -- `step-C-add↑` (§10), `step-D-add↑` (§10).
    IExpr-comp-PathP :
      {A A' : ℕ} (p : A ≡ A')
      {B : Fin A → ℕ} {B' : Fin A' → ℕ}
      (B-path : PathP (λ i → Fin (p i) → ℕ) B B')
      {e : IExpr A} {e' : IExpr A'}
      (e-path : PathP (λ i → IExpr (p i)) e e')
      {es : (a : Fin A) → IExpr (B a)} {es' : (a' : Fin A') → IExpr (B' a')}
      (es-path : PathP (λ i → (a : Fin (p i)) → IExpr (B-path i a)) es es')
      → PathP (λ i → IExpr (sum (p i) (B-path i)))
              (IExpr-comp A B e es) (IExpr-comp A' B' e' es')
    IExpr-comp-PathP p B-path e-path es-path i =
      IExpr-comp (p i) (B-path i) (e-path i) (es-path i)

    -- Alignment of `⅀Assoc-C' 𝓝 1 B C` with `C fzero` under the
    -- `+-zero (B fzero)` reindexing. Used in `B-path-id↑` (§9) to bridge
    -- the abstract assoc-coherence's family with the concrete `C fzero`.
    -- Proof: case-split on `_≤?_` inside `sumFinFwd 1 B`; the `inr`
    -- branch is impossible. Agda's `with` propagates the match into
    -- `sumFinFwd`, so the LHS of each clause reduces.
    ⅀Assoc-C'-id↑-eq :
      (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
      (a : Fin (B fzero + 0))
      → Universe.⅀Assoc-C' 𝓝 1 B C a
      ≡ C fzero (fst a , subst ((fst a) <_) (+-zero (B fzero)) (snd a))
    ⅀Assoc-C'-id↑-eq B C (k , prf) with k ≤? B fzero
    ... | inl k<m = cong (C fzero) (Fin-fst-≡ refl)
    ... | inr m≤k =
      absurd-≤? m≤k (subst (k <_) (+-zero (B fzero)) prf)

    -- The kss-application twin of `⅀Assoc-C'-id↑-eq`: a heterogeneous
    -- alignment of the abstract `kss-at-⅀Assoc-C'` function with the
    -- concrete `kss fzero` over the same `+-zero (B fzero)` reindexing,
    -- as a PathP over `IExpr` applied to `⅀Assoc-C'-id↑-eq`. Used by
    -- `es-path-id↑-pointwise` (§9).
    kss-id↑-PathP :
      (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
      (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
      (a : Fin (B fzero + 0))
      → PathP (λ i → IExpr (⅀Assoc-C'-id↑-eq B C a (~ i)))
              (kss fzero (fst a , subst ((fst a) <_) (+-zero (B fzero)) (snd a)))
              (kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a))
                    (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a)))
    kss-id↑-PathP B C kss (k , prf) with k ≤? B fzero
    ... | inl k<m =
      λ i → kss fzero (Fin-fst-≡ {i = (k , k<m)}
                                   {j = (k , subst (k <_) (+-zero (B fzero)) prf)}
                                   refl (~ i))
    ... | inr m≤k =
      absurd-≤? m≤k (subst (k <_) (+-zero (B fzero)) prf)

-- ============================================================================
-- §5  Left identity: `IExpr-idl`.
--
-- `IExpr-comp 1 (λ _ → A) id↑ (λ _ → k)` reduces definitionally to
-- `subst IExpr (sym (+-zero A)) k`. Recipe (a): "subst-filler reversal"
-- gives a PathP from this to `k` over `+-zero A`. Recipe (c): "isSetℕ
-- swap" replaces `+-zero A` by the desired `Inj 𝓝 (⅀Idl≃ A)`.
-- ============================================================================
opaque
  IExpr-idl : (A : ℕ) (k : IExpr A)
            → PathP (λ i → IExpr (Universe.Inj 𝓝 (Universe.⅀Idl≃ 𝓝 A) i))
                    (IExpr-comp 1 (λ _ → A) id↑ (λ _ → k)) k
  IExpr-idl A k =
    isSet→subst-PathP isSetℕ {B = IExpr}
                      (+-zero A) (Universe.Inj 𝓝 (Universe.⅀Idl≃ 𝓝 A))
                      (symP (subst-filler IExpr (sym (+-zero A)) k))

-- ============================================================================
-- §6  Right identity: `IExpr-idr`.
--
-- Induction on `k` gives three cases:
--   * `id↑` (A = 1): definitional reduction to `subst IExpr (sym (+-zero 1)) id↑`,
--     dispatched by recipe (a) + (c) like `IExpr-idl`.
--   * `val↑ n` (A = 0): definitionally `val↑ n` on both sides; the PathP
--     is `refl`, swapped via recipe (c).
--   * `add↑ e₁ e₂` (A = m + n): the LHS reduces to `subst IExpr (sym
--     (sum-split m n (λ _ → 1))) (add↑ recL recR)`. We compose
--     subst-filler reversal (the `sum-split` leg) with `cong add↑` of the
--     two per-fibre IHs.
-- ============================================================================
opaque
  IExpr-idr : (A : ℕ) (k : IExpr A)
            → PathP (λ i → IExpr (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 A) i))
                    (IExpr-comp A (λ _ → 1) k (λ _ → id↑)) k
  IExpr-idr .1 id↑ =
    isSet→subst-PathP isSetℕ {B = IExpr}
                      (+-zero 1) (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 1))
                      (symP (subst-filler IExpr (sym (+-zero 1)) id↑))
  IExpr-idr .0 (val↑ n) =
    isSet→subst-PathP isSetℕ {B = IExpr}
                      refl (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 0)) refl
  IExpr-idr .(m + n) (add↑ {m} {n} e₁ e₂) =
    isSet→subst-PathP isSetℕ {B = IExpr}
                      _ (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 (m + n)))
                      (compPathP' {B = IExpr} filler-path add↑-path)
    where
      recL : IExpr (sum m (λ _ → 1))
      recL = IExpr-comp m (λ _ → 1) e₁ (λ _ → id↑)
      recR : IExpr (sum n (λ _ → 1))
      recR = IExpr-comp n (λ _ → 1) e₂ (λ _ → id↑)
      lhs : IExpr (sum (m + n) (λ _ → 1))
      lhs = IExpr-comp (m + n) (λ _ → 1) (add↑ e₁ e₂) (λ _ → id↑)
      -- After definitional reduction lhs = subst IExpr (sym (sum-split …))
      -- (add↑ recL recR). Reverse the subst-filler.
      filler-path : PathP (λ i → IExpr (sum-split m n (λ _ → 1) i))
                          lhs (add↑ recL recR)
      filler-path = symP (subst-filler IExpr (sym (sum-split m n (λ _ → 1)))
                                            (add↑ recL recR))
      add↑-path : PathP (λ i → IExpr ( Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 m) i
                                     + Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 n) i))
                         (add↑ recL recR) (add↑ e₁ e₂)
      add↑-path i = add↑ (IExpr-idr m e₁ i) (IExpr-idr n e₂ i)

-- ============================================================================
-- §7  Joint-form toolkit for the add↑ case of associativity.
--
-- Recipe (d): "joint-form bridge" pattern. The `add↑` case of
-- `IExpr-assoc` needs to relate two views of the sum domain
-- `Fin (sum (m + n) B)`:
--   * the `(m+n)`-level view used by the abstract assoc statement
--     (with `⅀Assoc-C' 𝓝 (m + n) B C`);
--   * the `m + n`-flattened view used by the inductive proof (with
--     two halves built independently from `m` and `n`).
--
-- We define a "merged" family `joint-C'` and "merged" kss-application
-- `joint-kss` directly on `Fin (sum m (B ∘ inj-l-+ m n) + sum n (B ∘
-- inj-r-+ m n))` by case-split on `_≤?_`. The two `joint-…-on-inj-l-+`
-- / `…-on-inj-r-+` lemmas then bridge each half back to the m-side
-- (resp. n-side) form. These are the (m+n)-level analogues of
-- `⅀Assoc-C'-on-inl/-inr` and live next to them spiritually, but the
-- with-style implementation is operad-coloured (it commits to the
-- definitional case-split that `joint-…-on-inj-l-+/r` rely on for
-- their reductions), so they stay in this module.
--
-- The (m+n)-level Fubini lemmas `⅀Assoc-C'-add↑-on-l/r` come from
-- `HoTTOperads.Universe.Instances.Nat` (next to `⅀Assoc-C'-on-inl/-inr`);
-- the Fin/ℕ-level Fubini lemmas `sumFinFwd-add↑-on-l/r` and their
-- `sumFinFwd-suc-{inl,inr}-{fst,snd}` wrappers come from
-- `HoTTOperads.Prelude.Nat`.
-- ============================================================================

private
  opaque
    -- The merged family on `Fin (sum m Bₗ + sum n Bᵣ)`. Case-split on
    -- whether the flat index lies in the left half (`k < sum m Bₗ`) or
    -- the right half. The witness-bound on the right branch comes from
    -- `∸-<-lemma`. Used in `B-path-add↑(-pointwise)` (§8) as the joint
    -- target of the sum-split bridge, and in `joint-form-add↑` (§10).
    joint-C' : (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
             → Fin (sum m (B ∘ inj-l-+ m n) + sum n (B ∘ inj-r-+ m n)) → ℕ
    joint-C' m n B C (k , klt) with k ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl k<L = Universe.⅀Assoc-C' 𝓝 m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n) (k , k<L)
    ... | inr L≤k =
      Universe.⅀Assoc-C' 𝓝 n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n)
        (k ∸ sum m (B ∘ inj-l-+ m n)
        , ∸-<-lemma (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n)) k klt L≤k)

-- ============================================================================
-- §8  PathP toolkit for the (m+n)-Fubini side of associativity.
--
-- Three lemmas wire the joint-form (§7) into the abstract assoc PathP:
--   * `B-path-add↑(-pointwise)` — the family-PathP from
--     `⅀Assoc-C' 𝓝 (m+n) B C` to `joint-C' m n B C` over `sum-split m n B`.
--   * `es-path-add↑(-pointwise)` — the kss-application twin: a PathP
--     from the abstract `kss ∘ sumFinFwd` to `joint-kss m n B C kss`
--     over the same `sum-split` index path.
--   * `IExpr-comp-add↑-lemma` — pure subst-filler reversal at the
--     `IExpr-comp .(m + n) B (add↑ e₁ e₂) ks` reduction site.
-- All built via `funExtDep` of a pointwise alignment, with case-split
-- on `_≤?_` mirroring `joint-C'`'s.
-- ============================================================================

  opaque
    unfolding sum-split ⅀Assoc-C'-add↑-on-l ⅀Assoc-C'-add↑-on-r joint-C'

    -- Pointwise alignment for `B-path-add↑`'s `funExtDep`. Splits on
    -- whether the flat index lies in the left or right half; in each
    -- arm, bridges the input `Fin`-index by `Fin-fst-≡` and applies
    -- `⅀Assoc-C'-add↑-on-l/-on-r` to reach the half-side `⅀Assoc-C'`.
    B-path-add↑-pointwise :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
      (a₀ : Fin (sum (m + n) B)) (a₁ : Fin (sum m (B ∘ inj-l-+ m n) + sum n (B ∘ inj-r-+ m n)))
      (fst-eq : fst a₀ ≡ fst a₁)
      → Universe.⅀Assoc-C' 𝓝 (m + n) B C a₀ ≡ joint-C' m n B C a₁
    B-path-add↑-pointwise m n B C a₀ a₁ fst-eq
      with fst a₁ ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl k<L =
      let
        bridged-klt : fst a₁ < sum (m + n) B
        bridged-klt = subst (fst a₁ <_) (sym (sum-split m n B))
                             (o<m→o<m+n (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                          (fst a₁) k<L)
      in
        cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
             (Fin-fst-≡ {i = a₀} {j = (fst a₁ , bridged-klt)} fst-eq)
      ∙ ⅀Assoc-C'-add↑-on-l m n B C (fst a₁) k<L bridged-klt
    ... | inr L≤k =
      let
        k∸-bound : fst a₁ ∸ sum m (B ∘ inj-l-+ m n) < sum n (B ∘ inj-r-+ m n)
        k∸-bound = ∸-<-lemma (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                              (fst a₁) (snd a₁) L≤k
        bridged-klt : sum m (B ∘ inj-l-+ m n) + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n)) < sum (m + n) B
        bridged-klt = subst (sum m (B ∘ inj-l-+ m n) + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n)) <_)
                             (sym (sum-split m n B))
                             (<-k+ {k = sum m (B ∘ inj-l-+ m n)} k∸-bound)
        index-eq : fst a₀ ≡ sum m (B ∘ inj-l-+ m n) + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
        index-eq = fst-eq ∙ sym (∸-lemma L≤k)
      in
        cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
             (Fin-fst-≡ {i = a₀} {j = (sum m (B ∘ inj-l-+ m n) + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                                      , bridged-klt)}
                        index-eq)
      ∙ ⅀Assoc-C'-add↑-on-r m n B C (fst a₁ ∸ sum m (B ∘ inj-l-+ m n)) k∸-bound bridged-klt

    B-path-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                → PathP (λ i → Fin (sum-split m n B i) → ℕ)
                        (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                        (joint-C' m n B C)
    B-path-add↑ m n B C = funExtDep λ {a₀} {a₁} a-path →
      B-path-add↑-pointwise m n B C a₀ a₁
        (sym (transport-Fin-fst (sum-split m n B) a₀) ∙ cong fst (fromPathP a-path))

  -- The kss-application twin of `joint-C'`. Same case-split on
  -- `_≤?_`; in each branch, applies `sumFinFwd` to recover the
  -- underlying `(a, b)` Σ-pair, then calls `kss`. Used in
  -- `joint-form-add↑` (§10) and bridged to `kss ∘ sumFinFwd` via
  -- `es-path-add↑(-pointwise)` (§8).
  opaque
    unfolding joint-C'

    joint-kss : (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
              → (ab : Fin (sum m (B ∘ inj-l-+ m n) + sum n (B ∘ inj-r-+ m n)))
              → IExpr (joint-C' m n B C ab)
    joint-kss m n B C kss (k , klt) with k ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl k<L =
      kss (inj-l-+ m n (fst (sumFinFwd m (B ∘ inj-l-+ m n) (k , k<L))))
          (snd (sumFinFwd m (B ∘ inj-l-+ m n) (k , k<L)))
    ... | inr L≤k =
      kss (inj-r-+ m n
            (fst (sumFinFwd n (B ∘ inj-r-+ m n)
                              (k ∸ sum m (B ∘ inj-l-+ m n)
                              , ∸-<-lemma (sum m (B ∘ inj-l-+ m n))
                                            (sum n (B ∘ inj-r-+ m n)) k klt L≤k))))
          (snd (sumFinFwd n (B ∘ inj-r-+ m n)
                            (k ∸ sum m (B ∘ inj-l-+ m n)
                            , ∸-<-lemma (sum m (B ∘ inj-l-+ m n))
                                          (sum n (B ∘ inj-r-+ m n)) k klt L≤k)))

  -- The (m+n)-level Σ-pair Fubini lemmas `sumFinFwd-add↑-on-l/r` and
  -- their `sumFinFwd-suc-{inl,inr}-{fst,snd}` wrappers come from
  -- `HoTTOperads.Prelude.Nat`; we no longer redefine them here.


  -- "joint-form bridge" reductions: `joint-C'`/`joint-kss` restricted to
  -- `inj-l-+` or `inj-r-+` reduce to the m-side (resp. n-side)
  -- `⅀Assoc-C'` / kss-application. (m+n)-level analogues of
  -- `⅀Assoc-C'-on-inl/-inr`. Used as the bridge legs in `step-C-add↑` (§10).
  --
  -- The `inj-r-+` arm needs a propositional `(L+k ∸ L) ≡ k` bridge in
  -- `Fin (sum n (B ∘ inj-r-+ m n))`. We factor *both* the underlying
  -- ℕ-path and its `Fin-fst-≡` lift as shared `opaque` definitions so
  -- that:
  --   (1) `joint-C'-on-inj-r-+`'s family motive and `joint-kss-on-inj-r-+`'s
  --       PathP body reference the same opaque name, so type unification
  --       between them is by-name and trivial — no cubical face checks;
  --   (2) `Fin-fst-≡`'s body — which is `Σ≡Prop`-driven `transp` machinery
  --       and is *not* opaque in `Cubical.Data.Fin.Properties` — gets
  --       sealed at the `r-+-fin-bridge` boundary, instead of being
  --       re-normalised inside `joint-kss-on-inj-r-+`'s `cong` body.
  --
  -- Without these two `opaque` layers, `joint-kss-on-inj-r-+` alone
  -- typechecked in ~19s and accounted for ~75% of the entire module's
  -- cost. With them it typechecks in ~0.3s — a ~58× speedup that brings
  -- the module's total typecheck from ~25s to ~7s.

  opaque
    r-+-idx-bridge : (m n : ℕ) (B : Fin (m + n) → ℕ) (k : ℕ)
                   → sum m (B ∘ inj-l-+ m n) + k ∸ sum m (B ∘ inj-l-+ m n) ≡ k
    r-+-idx-bridge m n B k =
        cong (_∸ sum m (B ∘ inj-l-+ m n)) (+-comm (sum m (B ∘ inj-l-+ m n)) k)
      ∙ m+n∸n=m (sum m (B ∘ inj-l-+ m n)) k

  opaque
    r-+-fin-bridge : (m n : ℕ) (B : Fin (m + n) → ℕ)
                     (k : ℕ) (k<R-input : k < sum n (B ∘ inj-r-+ m n))
                     (L≤L+k : sum m (B ∘ inj-l-+ m n) ≤ sum m (B ∘ inj-l-+ m n) + k)
                   → _≡_ {A = Fin (sum n (B ∘ inj-r-+ m n))}
                          ( sum m (B ∘ inj-l-+ m n) + k ∸ sum m (B ∘ inj-l-+ m n)
                          , ∸-<-lemma (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                       (sum m (B ∘ inj-l-+ m n) + k)
                                       (<-k+ {k = sum m (B ∘ inj-l-+ m n)} k<R-input)
                                       L≤L+k)
                          (k , k<R-input)
    r-+-fin-bridge m n B k k<R-input L≤L+k = Fin-fst-≡ (r-+-idx-bridge m n B k)

  opaque
    unfolding joint-C'
    joint-C'-on-inj-l-+ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                       (kp : Fin (sum m (B ∘ inj-l-+ m n)))
                     → joint-C' m n B C
                         (inj-l-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n)) kp)
                     ≡ Universe.⅀Assoc-C' 𝓝 m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n) kp
    joint-C'-on-inj-l-+ m n B C (k , k<L-input)
      with k ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl k<L = cong (Universe.⅀Assoc-C' 𝓝 m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n))
                          (Fin-fst-≡ {i = (k , k<L)} {j = (k , k<L-input)} refl)
    ... | inr L≤k = absurd-≤? L≤k k<L-input

  opaque
    unfolding joint-C'
    joint-C'-on-inj-r-+ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                       (kp : Fin (sum n (B ∘ inj-r-+ m n)))
                     → joint-C' m n B C
                         (inj-r-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n)) kp)
                     ≡ Universe.⅀Assoc-C' 𝓝 n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n) kp
    joint-C'-on-inj-r-+ m n B C (k , k<R-input)
      with (sum m (B ∘ inj-l-+ m n) + k) ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl L+k<L = absurd-+-≤? {b = sum m (B ∘ inj-l-+ m n)} {k = k} L+k<L
    ... | inr L≤L+k =
      cong (Universe.⅀Assoc-C' 𝓝 n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n))
           (r-+-fin-bridge m n B k k<R-input L≤L+k)

  opaque
    unfolding joint-kss joint-C'-on-inj-l-+
    joint-kss-on-inj-l-+ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                        (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                        (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                        (kp : Fin (sum m (B ∘ inj-l-+ m n)))
                      → PathP (λ i → IExpr (joint-C'-on-inj-l-+ m n B C kp i))
                              (joint-kss m n B C kss
                                         (inj-l-+ (sum m (B ∘ inj-l-+ m n))
                                                (sum n (B ∘ inj-r-+ m n)) kp))
                              (kss (inj-l-+ m n (fst (sumFinFwd m (B ∘ inj-l-+ m n) kp)))
                                   (snd (sumFinFwd m (B ∘ inj-l-+ m n) kp)))
    joint-kss-on-inj-l-+ m n B C kss (k , k<L-input)
      with k ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl k<L =
      λ i →
        kss (inj-l-+ m n (fst (sumFinFwd m (B ∘ inj-l-+ m n)
                                       (Fin-fst-≡ {i = (k , k<L)}
                                                   {j = (k , k<L-input)} refl i))))
            (snd (sumFinFwd m (B ∘ inj-l-+ m n)
                              (Fin-fst-≡ {i = (k , k<L)}
                                          {j = (k , k<L-input)} refl i)))
    ... | inr L≤k = absurd-≤? L≤k k<L-input

  opaque
    unfolding joint-kss joint-C'-on-inj-r-+
    joint-kss-on-inj-r-+ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                        (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                        (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                        (kp : Fin (sum n (B ∘ inj-r-+ m n)))
                      → PathP (λ i → IExpr (joint-C'-on-inj-r-+ m n B C kp i))
                              (joint-kss m n B C kss
                                         (inj-r-+ (sum m (B ∘ inj-l-+ m n))
                                                (sum n (B ∘ inj-r-+ m n)) kp))
                              (kss (inj-r-+ m n (fst (sumFinFwd n (B ∘ inj-r-+ m n) kp)))
                                   (snd (sumFinFwd n (B ∘ inj-r-+ m n) kp)))
    joint-kss-on-inj-r-+ m n B C kss (k , k<R-input)
      with (sum m (B ∘ inj-l-+ m n) + k) ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl L+k<L = absurd-+-≤? {b = sum m (B ∘ inj-l-+ m n)} {k = k} L+k<L
    ... | inr L≤L+k =
      cong kss-applied (r-+-fin-bridge m n B k k<R-input L≤L+k)
      where
        -- The single-argument kss-application. `cong kss-applied
        -- (r-+-fin-bridge …)` is the entire PathP body. Both the
        -- family motive (`joint-C'-on-inj-r-+`) and this body reference
        -- the same opaque `r-+-fin-bridge`, so Agda's type unification
        -- is by-name and trivial — no cubical face checks required.
        kss-applied : (kp' : Fin (sum n (B ∘ inj-r-+ m n)))
                    → IExpr (Universe.⅀Assoc-C' 𝓝 n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n) kp')
        kss-applied kp' = kss (inj-r-+ m n (fst (sumFinFwd n (B ∘ inj-r-+ m n) kp')))
                              (snd (sumFinFwd n (B ∘ inj-r-+ m n) kp'))

  -- The kss-application twin of `B-path-add↑(-pointwise)`. Pointwise
  -- alignment splits on `_≤?_` like `B-path-add↑-pointwise`; in each
  -- arm assembles a four-leg `compPathP'` via the "step A→B→C→D"-style
  -- recipe (steps 1-4 here). Each step is one of: bridge the input
  -- `Fin`-index, apply `sumFinFwd-add↑-on-l/r`, apply `joint-kss-on-inj-…`,
  -- align the joint-`Fin`-index. The composite is then swapped onto the
  -- declared `B-path-add↑` motive via "isSetℕ swap" (recipe (c)).

  opaque
    unfolding sum-split

    es-path-add↑-pointwise :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
      (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
      {a₀ : Fin (sum (m + n) B)}
      {a₁ : Fin (sum m (B ∘ inj-l-+ m n) + sum n (B ∘ inj-r-+ m n))}
      (a-path : PathP (λ i → Fin (sum-split m n B i)) a₀ a₁)
      → PathP (λ i → IExpr (B-path-add↑ m n B C i (a-path i)))
              (kss (fst (sumFinFwd (m + n) B a₀)) (snd (sumFinFwd (m + n) B a₀)))
              (joint-kss m n B C kss a₁)
    es-path-add↑-pointwise m n B C kss {a₀} {a₁} a-path
      with fst a₁ ≤? sum m (B ∘ inj-l-+ m n)
    ... | inl k<L =
      let
        fst-eq : fst a₀ ≡ fst a₁
        fst-eq = sym (transport-Fin-fst (sum-split m n B) a₀)
               ∙ cong fst (fromPathP a-path)
        bridged-klt : fst a₁ < sum (m + n) B
        bridged-klt = subst (fst a₁ <_) (sym (sum-split m n B))
                             (o<m→o<m+n (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                          (fst a₁) k<L)
        -- Step 1: kss at a₀ → kss at (fst a₁, bridged-klt). Bridge via Fin-fst-≡ on input.
        step1 : PathP (λ i → IExpr (Universe.⅀Assoc-C' 𝓝 (m + n) B C
                                       (Fin-fst-≡ {i = a₀}
                                                   {j = (fst a₁ , bridged-klt)} fst-eq i)))
                       (kss (fst (sumFinFwd (m + n) B a₀))
                            (snd (sumFinFwd (m + n) B a₀)))
                       (kss (fst (sumFinFwd (m + n) B (fst a₁ , bridged-klt)))
                            (snd (sumFinFwd (m + n) B (fst a₁ , bridged-klt))))
        step1 i =
          kss (fst (sumFinFwd (m + n) B
                              (Fin-fst-≡ {i = a₀}
                                          {j = (fst a₁ , bridged-klt)} fst-eq i)))
              (snd (sumFinFwd (m + n) B
                              (Fin-fst-≡ {i = a₀}
                                          {j = (fst a₁ , bridged-klt)} fst-eq i)))
        -- Step 2: kss at (m+n) sFF → kss at inj-l-+ m n (m sFF). Bridge via sumFinFwd-add↑-on-l.
        sFF-on-l = sumFinFwd-add↑-on-l m n B (fst a₁) k<L bridged-klt
        step2 : PathP (λ i → IExpr (C (sFF-on-l .fst i) (sFF-on-l .snd i)))
                       (kss (fst (sumFinFwd (m + n) B (fst a₁ , bridged-klt)))
                            (snd (sumFinFwd (m + n) B (fst a₁ , bridged-klt))))
                       (kss (inj-l-+ m n (fst (sumFinFwd m (B ∘ inj-l-+ m n) (fst a₁ , k<L))))
                            (snd (sumFinFwd m (B ∘ inj-l-+ m n) (fst a₁ , k<L))))
        step2 i = kss (sFF-on-l .fst i) (sFF-on-l .snd i)
        -- Step 3: kss (inj-l-+ m n (fst sFF')) (snd sFF') → joint-kss kss (inj-l-+ ... (fst a₁, k<L)).
        --   Use symP of joint-kss-on-inj-l-+.
        step3 : PathP (λ i → IExpr (joint-C'-on-inj-l-+ m n B C (fst a₁ , k<L) (~ i)))
                       (kss (inj-l-+ m n (fst (sumFinFwd m (B ∘ inj-l-+ m n) (fst a₁ , k<L))))
                            (snd (sumFinFwd m (B ∘ inj-l-+ m n) (fst a₁ , k<L))))
                       (joint-kss m n B C kss
                                  (inj-l-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                         (fst a₁ , k<L)))
        step3 = symP (joint-kss-on-inj-l-+ m n B C kss (fst a₁ , k<L))
        -- Step 4: joint-kss (inj-l-+ ... (fst a₁, k<L)) → joint-kss a₁. Bridge via Fin-fst-≡.
        align-a₁ : inj-l-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n)) (fst a₁ , k<L) ≡ a₁
        align-a₁ = Fin-fst-≡ {i = inj-l-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                       (fst a₁ , k<L)}
                              {j = a₁} refl
        step4 : PathP (λ i → IExpr (joint-C' m n B C (align-a₁ i)))
                       (joint-kss m n B C kss
                                  (inj-l-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                         (fst a₁ , k<L)))
                       (joint-kss m n B C kss a₁)
        step4 i = joint-kss m n B C kss (align-a₁ i)
        composed : PathP (λ i → IExpr (((cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                                              (Fin-fst-≡ {i = a₀}
                                                          {j = (fst a₁ , bridged-klt)} fst-eq))
                                        ∙ (λ i → C (sFF-on-l .fst i) (sFF-on-l .snd i))
                                        ∙ (λ i → joint-C'-on-inj-l-+ m n B C
                                                    (fst a₁ , k<L) (~ i))
                                        ∙ cong (joint-C' m n B C) align-a₁) i))
                          (kss (fst (sumFinFwd (m + n) B a₀))
                               (snd (sumFinFwd (m + n) B a₀)))
                          (joint-kss m n B C kss a₁)
        composed = compPathP' {B = IExpr} step1
                     (compPathP' {B = IExpr} step2
                       (compPathP' {B = IExpr} step3 step4))
        target-path : Universe.⅀Assoc-C' 𝓝 (m + n) B C a₀ ≡ joint-C' m n B C a₁
        target-path = λ i → B-path-add↑ m n B C i (a-path i)
      in isSet→subst-PathP isSetℕ {B = IExpr}
           ((cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                  (Fin-fst-≡ {i = a₀}
                              {j = (fst a₁ , bridged-klt)} fst-eq))
            ∙ (λ i → C (sFF-on-l .fst i) (sFF-on-l .snd i))
            ∙ (λ i → joint-C'-on-inj-l-+ m n B C (fst a₁ , k<L) (~ i))
            ∙ cong (joint-C' m n B C) align-a₁)
           target-path
           composed
    ... | inr L≤k =
      let
        fst-eq : fst a₀ ≡ fst a₁
        fst-eq = sym (transport-Fin-fst (sum-split m n B) a₀)
               ∙ cong fst (fromPathP a-path)
        k∸-bound : fst a₁ ∸ sum m (B ∘ inj-l-+ m n) < sum n (B ∘ inj-r-+ m n)
        k∸-bound = ∸-<-lemma (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                              (fst a₁) (snd a₁) L≤k
        bridged-klt : sum m (B ∘ inj-l-+ m n) + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                    < sum (m + n) B
        bridged-klt = subst (sum m (B ∘ inj-l-+ m n) + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n)) <_)
                             (sym (sum-split m n B))
                             (<-k+ {k = sum m (B ∘ inj-l-+ m n)} k∸-bound)
        index-eq : fst a₀ ≡ sum m (B ∘ inj-l-+ m n) + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
        index-eq = fst-eq ∙ sym (∸-lemma L≤k)
        step1 : PathP (λ i → IExpr (Universe.⅀Assoc-C' 𝓝 (m + n) B C
                                       (Fin-fst-≡
                                          {i = a₀}
                                          {j = (sum m (B ∘ inj-l-+ m n)
                                                + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                                               , bridged-klt)}
                                          index-eq i)))
                       (kss (fst (sumFinFwd (m + n) B a₀))
                            (snd (sumFinFwd (m + n) B a₀)))
                       (kss (fst (sumFinFwd (m + n) B
                                            (sum m (B ∘ inj-l-+ m n)
                                             + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                                            , bridged-klt)))
                            (snd (sumFinFwd (m + n) B _)))
        step1 i =
          kss (fst (sumFinFwd (m + n) B
                              (Fin-fst-≡ {i = a₀}
                                          {j = (sum m (B ∘ inj-l-+ m n)
                                                + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                                               , bridged-klt)}
                                          index-eq i)))
              (snd (sumFinFwd (m + n) B
                              (Fin-fst-≡ {i = a₀}
                                          {j = (sum m (B ∘ inj-l-+ m n)
                                                + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                                               , bridged-klt)}
                                          index-eq i)))
        sFF-on-r = sumFinFwd-add↑-on-r m n B (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                                       k∸-bound bridged-klt
        step2 : PathP (λ i → IExpr (C (sFF-on-r .fst i) (sFF-on-r .snd i)))
                       (kss (fst (sumFinFwd (m + n) B
                                            (sum m (B ∘ inj-l-+ m n)
                                             + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                                            , bridged-klt)))
                            (snd (sumFinFwd (m + n) B _)))
                       (kss (inj-r-+ m n (fst (sumFinFwd n (B ∘ inj-r-+ m n)
                                                       (fst a₁ ∸ sum m (B ∘ inj-l-+ m n)
                                                       , k∸-bound))))
                            (snd (sumFinFwd n (B ∘ inj-r-+ m n) _)))
        step2 i = kss (sFF-on-r .fst i) (sFF-on-r .snd i)
        step3 : PathP (λ i → IExpr (joint-C'-on-inj-r-+ m n B C
                                       (fst a₁ ∸ sum m (B ∘ inj-l-+ m n) , k∸-bound) (~ i)))
                       (kss (inj-r-+ m n (fst (sumFinFwd n (B ∘ inj-r-+ m n)
                                                       (fst a₁ ∸ sum m (B ∘ inj-l-+ m n)
                                                       , k∸-bound))))
                            (snd (sumFinFwd n (B ∘ inj-r-+ m n) _)))
                       (joint-kss m n B C kss
                                  (inj-r-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                         (fst a₁ ∸ sum m (B ∘ inj-l-+ m n) , k∸-bound)))
        step3 = symP (joint-kss-on-inj-r-+ m n B C kss
                                         (fst a₁ ∸ sum m (B ∘ inj-l-+ m n) , k∸-bound))
        align-a₁ : inj-r-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                        (fst a₁ ∸ sum m (B ∘ inj-l-+ m n) , k∸-bound) ≡ a₁
        align-a₁ = Fin-fst-≡ {i = inj-r-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                        (fst a₁ ∸ sum m (B ∘ inj-l-+ m n) , k∸-bound)}
                              {j = a₁} (∸-lemma L≤k)
        step4 : PathP (λ i → IExpr (joint-C' m n B C (align-a₁ i)))
                       (joint-kss m n B C kss
                                  (inj-r-+ (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                                         (fst a₁ ∸ sum m (B ∘ inj-l-+ m n) , k∸-bound)))
                       (joint-kss m n B C kss a₁)
        step4 i = joint-kss m n B C kss (align-a₁ i)
        composed = compPathP' {B = IExpr} step1
                     (compPathP' {B = IExpr} step2
                       (compPathP' {B = IExpr} step3 step4))
        target-path : Universe.⅀Assoc-C' 𝓝 (m + n) B C a₀ ≡ joint-C' m n B C a₁
        target-path = λ i → B-path-add↑ m n B C i (a-path i)
      in isSet→subst-PathP isSetℕ {B = IExpr}
           ((cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                  (Fin-fst-≡
                     {i = a₀}
                     {j = (sum m (B ∘ inj-l-+ m n)
                           + (fst a₁ ∸ sum m (B ∘ inj-l-+ m n))
                          , bridged-klt)}
                     index-eq))
            ∙ (λ i → C (sFF-on-r .fst i) (sFF-on-r .snd i))
            ∙ (λ i → joint-C'-on-inj-r-+ m n B C
                        (fst a₁ ∸ sum m (B ∘ inj-l-+ m n) , k∸-bound) (~ i))
            ∙ cong (joint-C' m n B C) align-a₁)
           target-path
           composed

  opaque
    unfolding es-path-add↑-pointwise B-path-add↑ B-path-add↑-pointwise
    es-path-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                   (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                   (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                 → PathP (λ i → (a : Fin (sum-split m n B i))
                              → IExpr (B-path-add↑ m n B C i a))
                         (λ a → kss (fst (sumFinFwd (m + n) B a))
                                     (snd (sumFinFwd (m + n) B a)))
                         (joint-kss m n B C kss)
    es-path-add↑ m n B C kss = funExtDep (es-path-add↑-pointwise m n B C kss)

  -- "Subst-filler reversal" recipe (a) at the `IExpr-comp .(m+n) B
  -- (add↑ e₁ e₂) ks` reduction site. Distributes the outer
  -- `subst IExpr (sym (sum-split m n B))` over the inner `add↑`.
  -- Used as `step-D-add↑`'s IExpr-PathP argument (§10).

  opaque
    unfolding sum-split
    IExpr-comp-add↑-lemma : (m n : ℕ) (B : Fin (m + n) → ℕ)
                            (e₁ : IExpr m) (e₂ : IExpr n)
                            (ks : (a : Fin (m + n)) → IExpr (B a))
                          → PathP (λ i → IExpr (sum-split m n B (~ i)))
                                  (add↑ (IExpr-comp m (B ∘ inj-l-+ m n) e₁ (ks ∘ inj-l-+ m n))
                                        (IExpr-comp n (B ∘ inj-r-+ m n) e₂ (ks ∘ inj-r-+ m n)))
                                  (IExpr-comp (m + n) B (add↑ e₁ e₂) ks)
    IExpr-comp-add↑-lemma m n B e₁ e₂ ks =
      subst-filler IExpr (sym (sum-split m n B))
        (add↑ (IExpr-comp m (B ∘ inj-l-+ m n) e₁ (ks ∘ inj-l-+ m n))
              (IExpr-comp n (B ∘ inj-r-+ m n) e₂ (ks ∘ inj-r-+ m n)))

-- ============================================================================
-- §9  Associativity, id↑ case: `IExpr-assoc-id↑`.
--
-- Top-level statement: when the operadic source is `id↑ : IExpr 1`,
-- the abstract assoc PathP collapses (definitionally) to a `subst IExpr
-- (sym (+-zero (sum (B fzero) (C fzero))))`-style equation. We assemble
-- it as `outer-id↑ ∙ bridge-id↑` (recipe (a) + (b)), with index path
-- `chosen-path-id↑`, then "isSetℕ swap" (recipe (c)) onto the abstract
-- `Inj 𝓝 (⅀Assoc≃ 𝓝 1 B C)` index.
--
-- All helpers are pulled out to top-level and wrapped in `opaque`
-- blocks. They take `B, C, ks, kss` as parameters (matching the id↑
-- context). Each `opaque` block prevents the normaliser from unfolding
-- it when typechecking a later block.
-- ============================================================================

private
  opaque
    -- The aligning family-path between `C fzero` and `⅀Assoc-C' 𝓝 1 B C`,
    -- built via `funExtDep` using the `⅀Assoc-C'-id↑-eq` lemma (§4).
    B-path-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
               → PathP (λ i → Fin (sym (+-zero (B fzero)) i) → ℕ)
                       (C fzero) (Universe.⅀Assoc-C' 𝓝 1 B C)
    B-path-id↑ B C = funExtDep λ {a₀} {a₁} a-path →
      let fst-eq : fst a₀ ≡ fst a₁
          fst-eq = sym (transport-Fin-fst (sym (+-zero (B fzero))) a₀)
                  ∙ cong fst (fromPathP a-path)
      in cong (C fzero) (Fin-fst-≡ fst-eq)
       ∙ sym (⅀Assoc-C'-id↑-eq B C a₁)

  -- Pointwise alignment for `es-path-id↑`'s `funExtDep`, pulled out so
  -- Agda can chunk the heavy proof; `opaque` to seal the body. Two-step
  -- chain: bridge `kss fzero a₀` to `kss fzero (fst a₁ , …)` via
  -- `Fin-fst-≡` on the input, then apply `kss-id↑-PathP` (§4) to land
  -- at the abstract `kss ∘ ⟦⅀⟧⁻¹` form. "isSetℕ swap" onto the declared
  -- `B-path-id↑` motive.
  opaque
    es-path-id↑-pointwise :
      (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
      (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
      {a₀ : Fin (B fzero)} {a₁ : Fin (B fzero + 0)}
      (a-path : PathP (λ i → Fin (sym (+-zero (B fzero)) i)) a₀ a₁)
      → PathP (λ i → IExpr (B-path-id↑ B C i (a-path i)))
              (kss fzero a₀)
              (kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁))
                    (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁)))
    es-path-id↑-pointwise B C kss {a₀} {a₁} a-path =
      let fst-eq : fst a₀ ≡ fst a₁
          fst-eq = sym (transport-Fin-fst (sym (+-zero (B fzero))) a₀)
                  ∙ cong fst (fromPathP a-path)
          align-a₀ : a₀ ≡ (fst a₁ , subst ((fst a₁) <_) (+-zero (B fzero)) (snd a₁))
          align-a₀ = Fin-fst-≡ fst-eq
          step1 : PathP (λ i → IExpr (cong (C fzero) align-a₀ i))
                        (kss fzero a₀)
                        (kss fzero (fst a₁ , subst ((fst a₁) <_) (+-zero (B fzero)) (snd a₁)))
          step1 i = kss fzero (align-a₀ i)
          step2 : PathP (λ i → IExpr (⅀Assoc-C'-id↑-eq B C a₁ (~ i)))
                        (kss fzero (fst a₁ , subst ((fst a₁) <_) (+-zero (B fzero)) (snd a₁)))
                        (kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁))
                              (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁)))
          step2 = kss-id↑-PathP B C kss a₁
          composed-path : C fzero a₀ ≡ Universe.⅀Assoc-C' 𝓝 1 B C a₁
          composed-path = cong (C fzero) align-a₀
                        ∙ (λ i → ⅀Assoc-C'-id↑-eq B C a₁ (~ i))
          composed : PathP (λ i → IExpr (composed-path i))
                            (kss fzero a₀)
                            (kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁))
                                  (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁)))
          composed = compPathP' {B = IExpr} step1 step2
      in isSet→subst-PathP isSetℕ {B = IExpr}
           composed-path (λ i → B-path-id↑ B C i (a-path i))
           composed

  opaque
    unfolding es-path-id↑-pointwise
    -- The aligning dependent-function-path between `kss fzero` and the
    -- `⅀Assoc-C'`-indexed kss-application, by `funExtDep` of the
    -- pointwise alignment above.
    es-path-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                  (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
                → PathP (λ i → (a : Fin (sym (+-zero (B fzero)) i))
                              → IExpr (B-path-id↑ B C i a))
                        (kss fzero)
                        (λ ab → kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab))
                                    (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab)))
    es-path-id↑ B C kss = funExtDep (es-path-id↑-pointwise B C kss)

  -- `Xinner-id↑`/`lhs-id↑`/`rhs-id↑`: the three endpoints around which
  -- the id↑-case PathP is assembled. `Xinner-id↑` is the "inner"
  -- normal form `IExpr-comp (B fzero) (C fzero) (ks fzero) (kss fzero)`;
  -- `lhs-id↑` is `subst IExpr (sym (+-zero …)) Xinner-id↑` (= the LHS
  -- of the assoc PathP after unfolding `IExpr-comp 1 …`); `rhs-id↑`
  -- is the RHS using the abstract `⅀Assoc-C' 𝓝 1 B C` family.
  opaque
    Xinner-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                 (ks : (a : Fin 1) → IExpr (B a))
                 (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
               → IExpr (sum (B fzero) (C fzero))
    Xinner-id↑ B C ks kss = IExpr-comp (B fzero) (C fzero) (ks fzero) (kss fzero)

  opaque
    unfolding Xinner-id↑
    lhs-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
              (ks : (a : Fin 1) → IExpr (B a))
              (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
            → IExpr (sum (B fzero) (C fzero) + 0)
    lhs-id↑ B C ks kss =
      subst IExpr (sym (+-zero (sum (B fzero) (C fzero)))) (Xinner-id↑ B C ks kss)

  opaque
    rhs-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
              (ks : (a : Fin 1) → IExpr (B a))
              (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
            → IExpr (sum (B fzero + 0) (Universe.⅀Assoc-C' 𝓝 1 B C))
    rhs-id↑ B C ks kss =
      IExpr-comp (B fzero + 0) (Universe.⅀Assoc-C' 𝓝 1 B C)
                 (subst IExpr (sym (+-zero (B fzero))) (ks fzero))
                 (λ ab → kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab))
                              (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab)))

  -- The PathP from `Xinner-id↑` to `rhs-id↑` via `IExpr-comp-PathP`
  -- (recipe (b)) over `+-zero (B fzero)` and the family-path `B-path-id↑`.
  opaque
    unfolding Xinner-id↑ rhs-id↑ IExpr-comp-PathP
    bridge-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                 (ks : (a : Fin 1) → IExpr (B a))
                 (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
               → PathP (λ i → IExpr (sum (sym (+-zero (B fzero)) i) (B-path-id↑ B C i)))
                       (Xinner-id↑ B C ks kss)
                       (rhs-id↑ B C ks kss)
    bridge-id↑ B C ks kss =
      IExpr-comp-PathP (sym (+-zero (B fzero))) (B-path-id↑ B C)
                       (subst-filler IExpr (sym (+-zero (B fzero))) (ks fzero))
                       (es-path-id↑ B C kss)

  -- The PathP from `lhs-id↑` to `Xinner-id↑`: recipe (a)
  -- "subst-filler reversal" over `+-zero (sum (B fzero) (C fzero))`.
  opaque
    unfolding Xinner-id↑ lhs-id↑
    outer-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                (ks : (a : Fin 1) → IExpr (B a))
                (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
              → PathP (λ i → IExpr (+-zero (sum (B fzero) (C fzero)) i))
                      (lhs-id↑ B C ks kss) (Xinner-id↑ B C ks kss)
    outer-id↑ B C ks kss =
      symP (subst-filler IExpr (sym (+-zero (sum (B fzero) (C fzero))))
                              (Xinner-id↑ B C ks kss))

  -- Pure ℕ-equality witnessing the composed id↑-case index path. Sealed
  -- independently so `IExpr-assoc-id↑` treats it as a black box (the
  -- "isSetℕ swap" only needs the existence of *some* ℕ-path, not its body).
  opaque
    chosen-path-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                    → sum (B fzero) (C fzero) + 0
                    ≡ sum (B fzero + 0) (Universe.⅀Assoc-C' 𝓝 1 B C)
    chosen-path-id↑ B C =
      +-zero (sum (B fzero) (C fzero))
      ∙ (λ i → sum (sym (+-zero (B fzero)) i) (B-path-id↑ B C i))

  -- The composed PathP from `lhs-id↑` to `rhs-id↑` via `outer-id↑` then
  -- `bridge-id↑`. The declared return type *names* `chosen-path-id↑`
  -- (rather than inlining its body); this lets `IExpr-assoc-id↑`'s
  -- "isSetℕ swap" match its motive by name without unfolding
  -- `chosen-path-id↑`. The unfolding cost is paid here, once.
  opaque
    unfolding chosen-path-id↑
    my-PathP-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                   (ks : (a : Fin 1) → IExpr (B a))
                   (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
                 → PathP (λ i → IExpr (chosen-path-id↑ B C i))
                         (lhs-id↑ B C ks kss) (rhs-id↑ B C ks kss)
    my-PathP-id↑ B C ks kss =
      compPathP' {B = IExpr} (outer-id↑ B C ks kss) (bridge-id↑ B C ks kss)

  -- `IExpr-assoc-id↑` — the id↑ case of `IExpr-assoc`, assembled from
  -- the pieces above. Only `lhs-id↑`/`rhs-id↑` need unfolding (so the
  -- subst's motive matches the declared return type using `IExpr-comp`
  -- directly); `my-PathP-id↑` and `chosen-path-id↑` are consumed by
  -- reference, not pattern-matched.
  opaque
    unfolding lhs-id↑ rhs-id↑
    IExpr-assoc-id↑ : (B : Fin 1 → ℕ)
                      (C : (a : Fin 1) → Fin (B a) → ℕ)
                      (ks : (a : Fin 1) → IExpr (B a))
                      (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
                    → PathP (λ i → IExpr (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 1 B C) i))
                            (IExpr-comp 1 (λ a → sum (B a) (C a)) id↑
                                          (λ a → IExpr-comp (B a) (C a) (ks a) (kss a)))
                            (IExpr-comp (sum 1 B) (Universe.⅀Assoc-C' 𝓝 1 B C)
                                        (IExpr-comp 1 B id↑ ks)
                                        (λ ab → kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab))
                                                    (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab))))
    IExpr-assoc-id↑ B C ks kss =
      isSet→subst-PathP isSetℕ {B = IExpr}
        (chosen-path-id↑ B C) (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 1 B C))
        (my-PathP-id↑ B C ks kss)

-- ============================================================================
-- §10  Associativity, add↑ case: `IExpr-assoc-add↑`.
--
-- Recipe (e), the "step A→B→C→D" decomposition. Assembles the assoc
-- PathP as a four-leg `compPathP'`:
--
--   A : `lhs-add↑` ⟶ `add↑ Xinner-L Xinner-R`
--       Recipe (a): subst-filler reversal at the `IExpr-comp .(m+n)`
--       reduction site.
--   B : `add↑ Xinner-L Xinner-R` ⟶ `add↑ recL recR`
--       Apply per-fibre IHs `IH-L`, `IH-R` underneath `add↑`.
--   C : `add↑ recL recR` ⟶ `joint-form-add↑`
--       Recipe (d): joint-form bridges through `joint-C'-on-inj-l-+`
--       and `joint-kss-on-inj-l-+` (and the inj-r-+ twins).
--   D : `joint-form-add↑` ⟶ `rhs-add↑`
--       Recipe (b): `IExpr-comp-PathP` over the (m+n)-Fubini path
--       (`sum-split` + `B-path-add↑` + `es-path-add↑`).
--
-- Final "isSetℕ swap" (recipe (c)) sends the composite ℕ-path to the
-- abstract `Inj 𝓝 (⅀Assoc≃ 𝓝 (m+n) B C)` index path.
-- ============================================================================

private
  opaque
    -- The two "inner-target" intermediates, one per add↑-half. These
    -- are the LHS endpoints of `IH-L` / `IH-R` per-fibre IHs. Their
    -- normal forms appear under the `add↑` of step B; making them
    -- `opaque` prevents the normaliser from re-unfolding the per-fibre
    -- `IExpr-comp ∘ IExpr-comp` chain at every consumer.
    Xinner-L-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                    (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                    (e₁ : IExpr m)
                    (ks : (a : Fin (m + n)) → IExpr (B a))
                    (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                  → IExpr (sum m ((λ a → sum (B a) (C a)) ∘ inj-l-+ m n))
    Xinner-L-add↑ m n B C e₁ ks kss =
      IExpr-comp m ((λ a → sum (B a) (C a)) ∘ inj-l-+ m n) e₁
                 (λ a → IExpr-comp (B (inj-l-+ m n a)) (C (inj-l-+ m n a))
                                    (ks (inj-l-+ m n a)) (λ b → kss (inj-l-+ m n a) b))

    Xinner-R-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                    (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                    (e₂ : IExpr n)
                    (ks : (a : Fin (m + n)) → IExpr (B a))
                    (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                  → IExpr (sum n ((λ a → sum (B a) (C a)) ∘ inj-r-+ m n))
    Xinner-R-add↑ m n B C e₂ ks kss =
      IExpr-comp n ((λ a → sum (B a) (C a)) ∘ inj-r-+ m n) e₂
                 (λ a → IExpr-comp (B (inj-r-+ m n a)) (C (inj-r-+ m n a))
                                    (ks (inj-r-+ m n a)) (λ b → kss (inj-r-+ m n a) b))

  -- The RHS endpoints of the per-fibre IHs (`IH-L` / `IH-R`). Each is
  -- an `IExpr-comp` of the recursive (m-side / n-side) `IExpr-comp`
  -- over the `⅀Assoc-C'`-flattened family, with its kss-application
  -- restricted via `inj-l-+ m n` (resp. `inj-r-+ m n`).
  opaque
    recL-IHend-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                      (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                      (e₁ : IExpr m)
                      (ks : (a : Fin (m + n)) → IExpr (B a))
                      (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                    → IExpr (sum (sum m (B ∘ inj-l-+ m n))
                                  (Universe.⅀Assoc-C' 𝓝 m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n)))
    recL-IHend-add↑ m n B C e₁ ks kss =
      IExpr-comp (sum m (B ∘ inj-l-+ m n))
                 (Universe.⅀Assoc-C' 𝓝 m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n))
                 (IExpr-comp m (B ∘ inj-l-+ m n) e₁ (ks ∘ inj-l-+ m n))
                 (λ ab → kss (inj-l-+ m n (fst (sumFinFwd m (B ∘ inj-l-+ m n) ab)))
                              (snd (sumFinFwd m (B ∘ inj-l-+ m n) ab)))

    recR-IHend-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                      (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                      (e₂ : IExpr n)
                      (ks : (a : Fin (m + n)) → IExpr (B a))
                      (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                    → IExpr (sum (sum n (B ∘ inj-r-+ m n))
                                  (Universe.⅀Assoc-C' 𝓝 n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n)))
    recR-IHend-add↑ m n B C e₂ ks kss =
      IExpr-comp (sum n (B ∘ inj-r-+ m n))
                 (Universe.⅀Assoc-C' 𝓝 n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n))
                 (IExpr-comp n (B ∘ inj-r-+ m n) e₂ (ks ∘ inj-r-+ m n))
                 (λ ab → kss (inj-r-+ m n (fst (sumFinFwd n (B ∘ inj-r-+ m n) ab)))
                              (snd (sumFinFwd n (B ∘ inj-r-+ m n) ab)))

  -- The three principal endpoints of the add↑-case PathP. `lhs-add↑`
  -- is the `IExpr-assoc` LHS specialised to `add↑ e₁ e₂`; `rhs-add↑`
  -- the corresponding RHS; `joint-form-add↑` the intermediate
  -- joint-form value at which steps C and D meet. All three live in
  -- different `Fin (sum … )` types — this is the whole point of the
  -- step A→B→C→D decomposition: we *bridge* between them.
  opaque
    unfolding sum-split
    lhs-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
               (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
               (e₁ : IExpr m) (e₂ : IExpr n)
               (ks : (a : Fin (m + n)) → IExpr (B a))
               (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
             → IExpr (sum (m + n) (λ a → sum (B a) (C a)))
    lhs-add↑ m n B C e₁ e₂ ks kss =
      IExpr-comp (m + n) (λ a → sum (B a) (C a)) (add↑ e₁ e₂)
                 (λ a → IExpr-comp (B a) (C a) (ks a) (kss a))

    rhs-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
               (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
               (e₁ : IExpr m) (e₂ : IExpr n)
               (ks : (a : Fin (m + n)) → IExpr (B a))
               (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
             → IExpr (sum (sum (m + n) B) (Universe.⅀Assoc-C' 𝓝 (m + n) B C))
    rhs-add↑ m n B C e₁ e₂ ks kss =
      IExpr-comp (sum (m + n) B) (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                 (IExpr-comp (m + n) B (add↑ e₁ e₂) ks)
                 (λ ab → kss _ _)

    joint-form-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                      (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                      (e₁ : IExpr m) (e₂ : IExpr n)
                      (ks : (a : Fin (m + n)) → IExpr (B a))
                      (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                    → IExpr (sum (sum m (B ∘ inj-l-+ m n) + sum n (B ∘ inj-r-+ m n))
                                  (joint-C' m n B C))
    joint-form-add↑ m n B C e₁ e₂ ks kss =
      IExpr-comp (sum m (B ∘ inj-l-+ m n) + sum n (B ∘ inj-r-+ m n))
                 (joint-C' m n B C)
                 (add↑ (IExpr-comp m (B ∘ inj-l-+ m n) e₁ (ks ∘ inj-l-+ m n))
                       (IExpr-comp n (B ∘ inj-r-+ m n) e₂ (ks ∘ inj-r-+ m n)))
                 (joint-kss m n B C kss)

  -- **Step A** — recipe (a) "subst-filler reversal".
  -- `lhs-add↑` reduces (after `IExpr-comp` unfolds on `add↑ e₁ e₂`) to
  -- `subst IExpr (sym (sum-split m n …)) (add↑ Xinner-L Xinner-R)`.
  -- Reversing the subst-filler over `sum-split m n …` lifts this to a
  -- PathP from `lhs-add↑` to `add↑ Xinner-L Xinner-R`.
  opaque
    unfolding sum-split lhs-add↑ Xinner-L-add↑ Xinner-R-add↑
    step-A-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                  (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                  (e₁ : IExpr m) (e₂ : IExpr n)
                  (ks : (a : Fin (m + n)) → IExpr (B a))
                  (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                → PathP (λ i → IExpr (sum-split m n (λ a → sum (B a) (C a)) i))
                        (lhs-add↑ m n B C e₁ e₂ ks kss)
                        (add↑ (Xinner-L-add↑ m n B C e₁ ks kss)
                              (Xinner-R-add↑ m n B C e₂ ks kss))
    step-A-add↑ m n B C e₁ e₂ ks kss =
      symP (subst-filler IExpr (sym (sum-split m n (λ a → sum (B a) (C a))))
                                (add↑ (Xinner-L-add↑ m n B C e₁ ks kss)
                                      (Xinner-R-add↑ m n B C e₂ ks kss)))

  -- **Step B** — apply the per-fibre IHs `IH-L`, `IH-R` underneath
  -- `add↑`. Each IH is the recursive call `IExpr-assoc` on `e₁` (resp.
  -- `e₂`) at the half-side parameters; they're handed in by
  -- `IExpr-assoc-add↑` from `IExpr-assoc`'s top-level dispatch.
  opaque
    unfolding Xinner-L-add↑ Xinner-R-add↑ recL-IHend-add↑ recR-IHend-add↑
    step-B-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                  (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                  (e₁ : IExpr m) (e₂ : IExpr n)
                  (ks : (a : Fin (m + n)) → IExpr (B a))
                  (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                  (IH-L : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                (Universe.⅀Assoc≃ 𝓝 m (B ∘ inj-l-+ m n)
                                                                       (C ∘ inj-l-+ m n)) i))
                                (Xinner-L-add↑ m n B C e₁ ks kss)
                                (recL-IHend-add↑ m n B C e₁ ks kss))
                  (IH-R : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                (Universe.⅀Assoc≃ 𝓝 n (B ∘ inj-r-+ m n)
                                                                       (C ∘ inj-r-+ m n)) i))
                                (Xinner-R-add↑ m n B C e₂ ks kss)
                                (recR-IHend-add↑ m n B C e₂ ks kss))
                → PathP (λ i → IExpr ( Universe.Inj 𝓝
                                         (Universe.⅀Assoc≃ 𝓝 m (B ∘ inj-l-+ m n)
                                                                (C ∘ inj-l-+ m n)) i
                                       + Universe.Inj 𝓝
                                         (Universe.⅀Assoc≃ 𝓝 n (B ∘ inj-r-+ m n)
                                                                (C ∘ inj-r-+ m n)) i))
                        (add↑ (Xinner-L-add↑ m n B C e₁ ks kss)
                              (Xinner-R-add↑ m n B C e₂ ks kss))
                        (add↑ (recL-IHend-add↑ m n B C e₁ ks kss)
                              (recR-IHend-add↑ m n B C e₂ ks kss))
    step-B-add↑ m n B C e₁ e₂ ks kss IH-L IH-R i = add↑ (IH-L i) (IH-R i)

  -- **Step C** — recipe (d) "joint-form bridge". From
  -- `add↑ recL-IHend recR-IHend` we want the joint-form value
  -- `joint-form-add↑`, which packages the same data under
  -- `joint-C'`/`joint-kss`. We bridge via `IExpr-comp-PathP` whose
  -- family-path uses `joint-C'-on-inj-l-+` (resp. `…-on-inj-r-+`)
  -- backwards, and whose es-path uses the `joint-kss-on-inj-l-+`
  -- (resp. `…-on-inj-r-+`) twins; then reverse a final subst-filler
  -- over `sum-split (sum m Bₗ) (sum n Bᵣ) (joint-C' …)`.
  opaque
    unfolding sum-split recL-IHend-add↑ recR-IHend-add↑ joint-form-add↑
              IExpr-comp-PathP
    step-C-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                  (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                  (e₁ : IExpr m) (e₂ : IExpr n)
                  (ks : (a : Fin (m + n)) → IExpr (B a))
                  (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                → PathP (λ i → IExpr (((λ j →
                            sum (sum m (B ∘ inj-l-+ m n))
                                (λ kp → joint-C'-on-inj-l-+ m n B C kp (~ j))
                          + sum (sum n (B ∘ inj-r-+ m n))
                                (λ kp → joint-C'-on-inj-r-+ m n B C kp (~ j)))
                       ∙ sym (sum-split (sum m (B ∘ inj-l-+ m n))
                                        (sum n (B ∘ inj-r-+ m n))
                                        (joint-C' m n B C))) i))
                        (add↑ (recL-IHend-add↑ m n B C e₁ ks kss)
                              (recR-IHend-add↑ m n B C e₂ ks kss))
                        (joint-form-add↑ m n B C e₁ e₂ ks kss)
    step-C-add↑ m n B C e₁ e₂ ks kss =
      let
        innerL = IExpr-comp m (B ∘ inj-l-+ m n) e₁ (ks ∘ inj-l-+ m n)
        innerR = IExpr-comp n (B ∘ inj-r-+ m n) e₂ (ks ∘ inj-r-+ m n)
        bridge-L : PathP (λ i → IExpr (sum (sum m (B ∘ inj-l-+ m n))
                                             (λ kp → joint-C'-on-inj-l-+ m n B C kp (~ i))))
                          (recL-IHend-add↑ m n B C e₁ ks kss)
                          (IExpr-comp (sum m (B ∘ inj-l-+ m n))
                                      (λ kp → joint-C' m n B C
                                                 (inj-l-+ (sum m (B ∘ inj-l-+ m n))
                                                        (sum n (B ∘ inj-r-+ m n)) kp))
                                      innerL
                                      (λ kp → joint-kss m n B C kss
                                                 (inj-l-+ (sum m (B ∘ inj-l-+ m n))
                                                        (sum n (B ∘ inj-r-+ m n)) kp)))
        bridge-L = IExpr-comp-PathP refl
                                     (λ i kp → joint-C'-on-inj-l-+ m n B C kp (~ i))
                                     {e = innerL} {e' = innerL} (λ _ → innerL)
                                     (λ i kp → joint-kss-on-inj-l-+ m n B C kss kp (~ i))
        bridge-R : PathP (λ i → IExpr (sum (sum n (B ∘ inj-r-+ m n))
                                             (λ kp → joint-C'-on-inj-r-+ m n B C kp (~ i))))
                          (recR-IHend-add↑ m n B C e₂ ks kss)
                          (IExpr-comp (sum n (B ∘ inj-r-+ m n))
                                      (λ kp → joint-C' m n B C
                                                 (inj-r-+ (sum m (B ∘ inj-l-+ m n))
                                                        (sum n (B ∘ inj-r-+ m n)) kp))
                                      innerR
                                      (λ kp → joint-kss m n B C kss
                                                 (inj-r-+ (sum m (B ∘ inj-l-+ m n))
                                                        (sum n (B ∘ inj-r-+ m n)) kp)))
        bridge-R = IExpr-comp-PathP refl
                                     (λ i kp → joint-C'-on-inj-r-+ m n B C kp (~ i))
                                     {e = innerR} {e' = innerR} (λ _ → innerR)
                                     (λ i kp → joint-kss-on-inj-r-+ m n B C kss kp (~ i))
        bridge-LR i = add↑ (bridge-L i) (bridge-R i)
        sub-step-2 = subst-filler IExpr
                       (sym (sum-split (sum m (B ∘ inj-l-+ m n))
                                         (sum n (B ∘ inj-r-+ m n))
                                         (joint-C' m n B C)))
                       (add↑ (IExpr-comp (sum m (B ∘ inj-l-+ m n))
                                         (λ kp → joint-C' m n B C
                                                    (inj-l-+ (sum m (B ∘ inj-l-+ m n))
                                                           (sum n (B ∘ inj-r-+ m n)) kp))
                                         innerL
                                         (λ kp → joint-kss m n B C kss
                                                    (inj-l-+ (sum m (B ∘ inj-l-+ m n))
                                                           (sum n (B ∘ inj-r-+ m n)) kp)))
                             (IExpr-comp (sum n (B ∘ inj-r-+ m n))
                                         (λ kp → joint-C' m n B C
                                                    (inj-r-+ (sum m (B ∘ inj-l-+ m n))
                                                           (sum n (B ∘ inj-r-+ m n)) kp))
                                         innerR
                                         (λ kp → joint-kss m n B C kss
                                                    (inj-r-+ (sum m (B ∘ inj-l-+ m n))
                                                           (sum n (B ∘ inj-r-+ m n)) kp))))
      in compPathP' {B = IExpr} bridge-LR sub-step-2

  -- **Step D** — recipe (b) "`IExpr-comp-PathP` cong". From the joint
  -- form to the abstract `rhs-add↑` form, applying `IExpr-comp-PathP`
  -- through the (m+n)-Fubini paths `sum-split` and `B-path-add↑` (with
  -- `IExpr-comp-add↑-lemma` providing the IExpr-PathP and
  -- `es-path-add↑` the dependent-function-PathP, both reversed via `symP`).
  opaque
    unfolding sum-split joint-form-add↑ rhs-add↑ IExpr-comp-PathP
    step-D-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                  (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                  (e₁ : IExpr m) (e₂ : IExpr n)
                  (ks : (a : Fin (m + n)) → IExpr (B a))
                  (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                → PathP (λ i → IExpr (sum (sym (sum-split m n B) i)
                                            (symP (B-path-add↑ m n B C) i)))
                        (joint-form-add↑ m n B C e₁ e₂ ks kss)
                        (rhs-add↑ m n B C e₁ e₂ ks kss)
    step-D-add↑ m n B C e₁ e₂ ks kss =
      IExpr-comp-PathP (sym (sum-split m n B))
                       (symP (B-path-add↑ m n B C))
                       (IExpr-comp-add↑-lemma m n B e₁ e₂ ks)
                       (symP (es-path-add↑ m n B C kss))

  -- The composed ℕ-equality witnessing the add↑-case index path.
  -- Sealed independently so `IExpr-assoc-add↑` treats it as a black box
  -- (the "isSetℕ swap" only needs the existence of *some* ℕ-path).
  opaque
    chosen-path-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                     → sum (m + n) (λ a → sum (B a) (C a))
                     ≡ sum (sum (m + n) B) (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
    chosen-path-add↑ m n B C =
        sum-split m n (λ a → sum (B a) (C a))
      ∙ (λ i → ( Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n)) i
               + Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n)) i))
      ∙ ((λ j →
            sum (sum m (B ∘ inj-l-+ m n))
                (λ kp → joint-C'-on-inj-l-+ m n B C kp (~ j))
          + sum (sum n (B ∘ inj-r-+ m n))
                (λ kp → joint-C'-on-inj-r-+ m n B C kp (~ j)))
        ∙ sym (sum-split (sum m (B ∘ inj-l-+ m n)) (sum n (B ∘ inj-r-+ m n))
                          (joint-C' m n B C)))
      ∙ (λ i → sum (sym (sum-split m n B) i) (symP (B-path-add↑ m n B C) i))

  -- The four-leg composite. Uses step-A..D as opaque values, just
  -- chained via `compPathP'`; their bodies aren't needed to typecheck
  -- this chain. Only `chosen-path-add↑` must be unfolded so the
  -- assembled path matches the declared return-type's path family by
  -- definitional equality.
  opaque
    unfolding chosen-path-add↑

    composite-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                     (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                     (e₁ : IExpr m) (e₂ : IExpr n)
                     (ks : (a : Fin (m + n)) → IExpr (B a))
                     (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                     (IH-L : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                    (Universe.⅀Assoc≃ 𝓝 m (B ∘ inj-l-+ m n)
                                                                           (C ∘ inj-l-+ m n)) i))
                                    (Xinner-L-add↑ m n B C e₁ ks kss)
                                    (recL-IHend-add↑ m n B C e₁ ks kss))
                     (IH-R : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                    (Universe.⅀Assoc≃ 𝓝 n (B ∘ inj-r-+ m n)
                                                                           (C ∘ inj-r-+ m n)) i))
                                    (Xinner-R-add↑ m n B C e₂ ks kss)
                                    (recR-IHend-add↑ m n B C e₂ ks kss))
                   → PathP (λ i → IExpr (chosen-path-add↑ m n B C i))
                           (lhs-add↑ m n B C e₁ e₂ ks kss)
                           (rhs-add↑ m n B C e₁ e₂ ks kss)
    composite-add↑ m n B C e₁ e₂ ks kss IH-L IH-R =
      compPathP' {B = IExpr} (step-A-add↑ m n B C e₁ e₂ ks kss)
        (compPathP' {B = IExpr} (step-B-add↑ m n B C e₁ e₂ ks kss IH-L IH-R)
          (compPathP' {B = IExpr} (step-C-add↑ m n B C e₁ e₂ ks kss)
                                   (step-D-add↑ m n B C e₁ e₂ ks kss)))

  -- `IExpr-assoc-add↑` — the add↑ case of `IExpr-assoc`, packaged as
  -- the abstract assoc PathP via "isSetℕ swap" (recipe (c)). Only
  -- `lhs-add↑`/`rhs-add↑` need unfolding so the subst's motive matches
  -- the declared return type. `composite-add↑` is passed as a value
  -- (its type matches the motive by name); `chosen-path-add↑` is
  -- referenced only inside `isSetℕ` where syntactic equality suffices.
  opaque
    unfolding lhs-add↑ rhs-add↑

    IExpr-assoc-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                       (e₁ : IExpr m) (e₂ : IExpr n)
                       (ks : (a : Fin (m + n)) → IExpr (B a))
                       (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                       (IH-L : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                      (Universe.⅀Assoc≃ 𝓝 m (B ∘ inj-l-+ m n)
                                                                             (C ∘ inj-l-+ m n)) i))
                                      (Xinner-L-add↑ m n B C e₁ ks kss)
                                      (recL-IHend-add↑ m n B C e₁ ks kss))
                       (IH-R : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                      (Universe.⅀Assoc≃ 𝓝 n (B ∘ inj-r-+ m n)
                                                                             (C ∘ inj-r-+ m n)) i))
                                      (Xinner-R-add↑ m n B C e₂ ks kss)
                                      (recR-IHend-add↑ m n B C e₂ ks kss))
                     → PathP (λ i → IExpr (Universe.Inj 𝓝
                                              (Universe.⅀Assoc≃ 𝓝 (m + n) B C) i))
                             (IExpr-comp (m + n) (λ a → sum (B a) (C a)) (add↑ e₁ e₂)
                                         (λ a → IExpr-comp (B a) (C a) (ks a) (kss a)))
                             (IExpr-comp (sum (m + n) B)
                                         (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                                         (IExpr-comp (m + n) B (add↑ e₁ e₂) ks)
                                         (λ ab → kss _ _))
    IExpr-assoc-add↑ m n B C e₁ e₂ ks kss IH-L IH-R =
      isSet→subst-PathP isSetℕ {B = IExpr}
        (chosen-path-add↑ m n B C)
        (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 (m + n) B C))
        (composite-add↑ m n B C e₁ e₂ ks kss IH-L IH-R)

-- ============================================================================
-- §11  Top-level associativity dispatch: `IExpr-assoc`.
--
-- Induction on the IExpr argument:
--   * `val↑` (A = 0): both sides are definitionally `val↑ n`; the PathP
--     is `refl`, swapped via "isSetℕ swap".
--   * `id↑`  (A = 1): `IExpr-assoc-id↑` (§9).
--   * `add↑` (A = m + n): `IExpr-assoc-add↑` (§10), with the per-fibre
--     IHs supplied by recursive calls.
--
-- The four IH-endpoint definitions of §10 are unfolded in this clause
-- so the subst's motive matches the declared return type by name. Do
-- not move them out of the unfolding list — `IExpr-assoc-add↑`'s
-- `IH-L`/`IH-R` PathP types are stated in terms of those names.
-- ============================================================================
opaque
  unfolding Xinner-L-add↑ Xinner-R-add↑ recL-IHend-add↑ recR-IHend-add↑
  IExpr-assoc : (A : ℕ) (B : Fin A → ℕ)
                (C : (a : Fin A) → Fin (B a) → ℕ)
                (k : IExpr A) (ks : (a : Fin A) → IExpr (B a))
                (kss : (a : Fin A) (b : Fin (B a)) → IExpr (C a b))
              → PathP (λ i → IExpr (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 A B C) i))
                      (IExpr-comp A (λ a → sum (B a) (C a)) k
                                  (λ a → IExpr-comp (B a) (C a) (ks a) (kss a)))
                      (IExpr-comp (sum A B) (Universe.⅀Assoc-C' 𝓝 A B C)
                                  (IExpr-comp A B k ks)
                                  (λ ab → kss _ _))
  IExpr-assoc .0 B C (val↑ n) ks kss =
    isSet→subst-PathP isSetℕ {B = IExpr}
      refl (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 0 B C))
      refl
  IExpr-assoc .1 B C id↑ ks kss = IExpr-assoc-id↑ B C ks kss
  IExpr-assoc .(m + n) B C (add↑ {m} {n} e₁ e₂) ks kss =
    IExpr-assoc-add↑ m n B C e₁ e₂ ks kss
      (IExpr-assoc m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n) e₁
                   (ks ∘ inj-l-+ m n) (λ a → kss (inj-l-+ m n a)))
      (IExpr-assoc n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n) e₂
                   (ks ∘ inj-r-+ m n) (λ a → kss (inj-r-+ m n a)))

-- ============================================================================
-- §12  Operad assembly: `IExprOperad`.
--
-- Bundle the components into the `Operad 𝓝 IExpr = NonSymmOperad IExpr`
-- record. This is the public API of the module.
-- ============================================================================
IExprOperad : NonSymmOperad IExpr
Operad.isSetK IExprOperad = isSetIExpr
Operad.id     IExprOperad = id↑
Operad.compₒ  IExprOperad = IExpr-comp
Operad.idl    IExprOperad = IExpr-idl
Operad.idr    IExprOperad = IExpr-idr
Operad.assoc  IExprOperad = IExpr-assoc
