{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Universe.Instances.Nat
--
-- The non-symmetric operad universe `𝓝 : Universe ℓ-zero ℓ-zero` on the
-- arithmetic skeleton `(Code = ℕ, El = Fin, ⅀ = sum, 𝜏 = 1)`. The construction
-- splits into two halves: the base record `𝓝-base` (cheap — a bundle of
-- arithmetic data and library equivalences), and the coherence record
-- `𝓝-coh` (the bulk of this file). Every coherence is discharged via a
-- single recipe: show that the equivalence's forward function preserves the
-- underlying ℕ-projection `fst`, then invoke `coh-from-fst` to lift that
-- fact through `equivFin-by-fst`, `ua-pathToEquiv`, and the set-hood of `ℕ`.
-- The hard case is associativity, which goes via a Fubini identity on
-- prefix sums.
--
-- ## File layout
--
--   §1  Imports and `Fin1≃Unit`.
--   §2  `NatInj`, `NatInjComp`, and the `𝓝-base` record.
--   §3  The coherence recipe `coh-from-fst` (recipe (a)).
--   §4  Unit coherences: `⅀Idl-preserves-fst`, `⅀Idr-preserves-fst`.
--   §5  Associativity, suc-level slice: `⅀Assoc-C'-on-inl`,
--       `⅀Assoc-C'-on-inr` (public; consumed by IExpr.agda, PartialList.agda).
--   §6  Associativity, (m+n)-level slice: `⅀Assoc-C'-add↑-on-l`,
--       `⅀Assoc-C'-add↑-on-r` (public; consumed by IExpr.agda).
--   §7  Fubini identity: `sum-prefix-ℕ-PathP`, `fubini`.
--   §8  Forward fst-preservation via the `invEq` trace:
--       `⅀Assoc-preserves-fst-INV`, `⅀Assoc-preserves-fst`.
--   §9  Universe assembly: `𝓝-coh`, `𝓝`.
--
-- ## Recipes
--
--   (a) fst-preservation → coherence. Given `e : Fin n ≃ Fin m` whose
--       forward function preserves `fst`, `coh-from-fst e p hyp` produces
--       the path `ua e ≡ cong Fin (NatInj e)` for any chosen `p : n ≡ m`.
--       The choice of `p` is immaterial because `isSetℕ` collapses any
--       two ℕ-paths. Used three times in §9 — once per coherence law.
--
--   (b) Fubini-via-induction. Inside `fubini` (§7), the `suc A'` clause
--       splits `sum-prefix-ℕ (B fzero + sum A' (B ∘ fsuc))` into the full
--       `B fzero`-block (left summand) plus a recursive sub-problem on
--       `B ∘ fsuc` (right summand). The IH closes the recursion at `A'`;
--       reassembly bridges the two halves via associativity of `+` and the
--       suc-level lemmas of §5.
--
--   (c) `with k ≤? bound` exhaustion. Every `⅀Assoc-C'-…` lemma in §5/§6
--       case-splits on `k ≤? B fzero` (or its (m+n)-lifted variant). The
--       impossible branch is closed by `absurd-≤?` or `absurd-+-≤?`. The
--       `-on-inl` / `-on-inr` / `-on-l` / `-on-r` suffixes name the branch
--       in which the lemma fires.
--
--   (d) Family-reindex bridge. The (m+n)-level proofs in §6 repeatedly
--       need to bridge `(B ∘ fsuc) ∘ inj-l-+ m' n a` and
--       `(B ∘ inj-l-+ (suc m') n) ∘ fsuc a`. Both are equal up to
--       `Fin-fst-≡ refl` on each input; the bridge is always
--       `cong B (Fin-fst-≡ refl)` lifted to a `funExt` over the family,
--       optionally chased by a `subst`/`ΣPathP` on the bound proof.
-- ============================================================================
module HoTTOperads.Universe.Instances.Nat where

-- ----------------------------------------------------------------------------
-- §1  Imports and `Fin1≃Unit`
-- ----------------------------------------------------------------------------
--
-- The `Prelude.Nat` names re-exported `public` below are consumed by
-- `PartialList.agda` (via `inj-l-+`, `inj-r-+`, `sumFinFwd`) and
-- `IExpr.agda` (via `sum`) through this module.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; pred-≤-pred ; ¬m<m ; ≤<-trans ; zero-≤
                                          ; ¬-<-zero ; ≤-trans ; suc-≤-suc ; isProp≤
                                          ; <-weaken ; <-k+ ; <-k+-cancel)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Fin.Properties using (Fin-inj ; isContrFin1 ; Fin-fst-≡ ; _≤?_
                                              ; isSetFin ; o<m→o<m+n ; ∸-<-lemma
                                              ; ∸-lemma ; m+n∸n=m)
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-fst ; Σ≡Prop)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using () renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit ; tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Prelude.Nat public using
  ( sum ; sum-idr ; sumFinEquiv ; equivFin-by-fst
  ; sum-prefix ; sum-prefix-ℕ ; sum-prefix-≡
  ; sumFinFwd ; sumFinBwd ; sumFinFwd-Bwd ; sumFinBwd-Fwd
  ; sum-prefix-ℕ-l ; sum-prefix-ℕ-r ; sum-prefix-ℕ-cong ; sum-cong
  ; sum≡sum-prefix-ℕ ; inj-l-+ ; inj-r-+ ; absurd-≤? ; absurd-+-≤? )

-- The unique inhabitant `fzero : Fin 1` is a contractible centre, so
-- `Fin 1 ≃ Unit`. Kept transparent: `UniverseBase.⟦𝜏⟧` reads the
-- `.equiv-proof` field to compute inverses of the identity equivalence.
Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = isoToEquiv (isContr→Iso isContrFin1 (tt , λ _ → refl))

-- ----------------------------------------------------------------------------
-- §2  `NatInj`, `NatInjComp`, and the base record `𝓝-base`
-- ----------------------------------------------------------------------------
--
-- `Inj` and `InjComp` are the two universe-of-codes obligations: any
-- equivalence between `Fin`-types must produce a path between the
-- ℕ-indices, and that path must distribute over equivalence composition.
-- Both are trivialised because `ℕ` is a set: `Fin-inj ∘ ua` produces the
-- path, and `isSetℕ` collapses any two parallel ℕ-paths.

opaque
  -- Injectivity of `Fin`: an equivalence of `Fin`-types lifts to a
  -- path of ℕ-indices via `ua` and `Fin-inj`.
  NatInj : {n m : ℕ} → Fin n ≃ Fin m → n ≡ m
  NatInj {n} {m} e = Fin-inj n m (ua e)

  -- Compositionality of `NatInj`. Free from `isSetℕ` — both sides land
  -- in `ℕ`, where parallel paths are uniquely identified.
  NatInjComp : {n m k : ℕ} (e₁ : Fin n ≃ Fin m) (e₂ : Fin m ≃ Fin k)
             → NatInj (compEquiv e₁ e₂) ≡ NatInj e₁ ∙ NatInj e₂
  NatInjComp _ _ = isSetℕ _ _ _ _

-- The base (non-coherent) part. Fields come from:
--   `Code`/`⅀` (`ℕ`/`sum`)  ............................ `Cubical.Data.Nat` + `Prelude.Nat`
--   `El`/`𝜏`/`⟦⅀⟧`/`⟦𝜏⟧`   ............................ `Cubical.Data.Fin` + local `Fin1≃Unit`
--   `Inj`/`InjComp`                                       local (this §)
𝓝-base : UniverseBase ℓ-zero ℓ-zero
UniverseBase.Code     𝓝-base = ℕ
UniverseBase.El       𝓝-base = Fin
UniverseBase.⅀        𝓝-base = sum
UniverseBase.𝜏        𝓝-base = 1
UniverseBase.⟦⅀⟧      𝓝-base = sumFinEquiv
UniverseBase.⟦𝜏⟧      𝓝-base = Fin1≃Unit
UniverseBase.Inj      𝓝-base = NatInj
UniverseBase.InjComp  𝓝-base = NatInjComp

-- ----------------------------------------------------------------------------
-- §3  The coherence recipe `coh-from-fst` (recipe (a))
-- ----------------------------------------------------------------------------
--
-- For each `e ∈ {⅀Idl≃ A, ⅀Idr≃ A, ⅀Assoc≃ A B C}` we will show that `e`
-- preserves the underlying ℕ-index (`fst ∘ equivFun e ≡ fst`). The recipe
-- `coh-from-fst` then lifts that fact to a path `ua e ≡ cong Fin (NatInj e)`
-- as follows: `equivFin-by-fst` turns the fst-preservation hypothesis into
-- `e ≡ pathToEquiv (cong Fin p)` for any chosen `p : n ≡ m`; congruence on
-- `ua` and `ua-pathToEquiv` collapse the LHS to `cong Fin p`; the choice
-- of `p` is then immaterial — `isSetℕ` identifies it with `NatInj e`. The
-- three universe coherences §4–§8 each plug into this recipe.

open UniverseBase 𝓝-base using (⅀Idl≃ ; ⅀Idr≃ ; ⅀Assoc≃ ; ⅀Assoc-C')

opaque
  -- The recipe itself. `p` is any convenient ℕ-path; `isSetℕ` will
  -- discharge any difference from `NatInj e`.
  coh-from-fst : {n m : ℕ} (e : Fin n ≃ Fin m) (p : n ≡ m)
               → ((k : Fin n) → fst (equivFun e k) ≡ fst k)
               → ua e ≡ cong Fin (NatInj e)
  coh-from-fst {n} {m} e p hyp =
    ua e
      ≡⟨ cong ua (equivFin-by-fst e p hyp) ⟩
    ua (pathToEquiv (cong Fin p))
      ≡⟨ ua-pathToEquiv (cong Fin p) ⟩
    cong Fin p
      ≡⟨ cong (cong Fin) (isSetℕ _ _ p (NatInj e)) ⟩
    cong Fin (NatInj e) ∎

-- ----------------------------------------------------------------------------
-- §4  Unit coherences: `⅀Idl-preserves-fst`, `⅀Idr-preserves-fst`
-- ----------------------------------------------------------------------------
--
-- The left-identity equivalence `⅀Idl≃ A : Fin (sum 1 (λ _ → A)) ≃ Fin A`
-- and right-identity `⅀Idr≃ A : Fin (sum A (λ _ → 1)) ≃ Fin A` are
-- shown to preserve the underlying ℕ-index. Each case-split exhausts a
-- `_≤?_` test (recipe (c)): the "real" branch returns `refl`/`cong suc`,
-- while the impossible branch is closed by `absurd-≤?` or `¬-<-zero`.

opaque
  -- Idl: `equivFun (⅀Idl≃ A)` reduces to the obvious left-cancellation,
  -- so the `m ≤? A` test always lands in `inl` (the `inr` arm gives
  -- `A ≤ m` against the bound `m < A + 0`).
  ⅀Idl-preserves-fst : (A : ℕ) (k : Fin (sum 1 (λ _ → A)))
                     → fst (equivFun (⅀Idl≃ A) k) ≡ fst k
  ⅀Idl-preserves-fst A (m , p) with m ≤? A
  ... | inl _    = refl
  ... | inr m≥A  = absurd-≤? m≥A (subst (m <_) (+-zero A) p)

  -- Idr: induction on `A`. The `zero` case is impossible (bound goes to
  -- `Fin 0`). The `suc A` case splits by `k ≤? 1`: the `zero` block
  -- returns `refl`; the recursive case folds via the IH and `cong suc`.
  ⅀Idr-preserves-fst : (A : ℕ) (k : Fin (sum A (λ _ → 1)))
                     → fst (equivFun (⅀Idr≃ A) k) ≡ fst k
  ⅀Idr-preserves-fst zero      (_     , p)   = ⊥-rec (¬-<-zero p)
  ⅀Idr-preserves-fst (suc A)   (zero  , p) with zero ≤? 1
  ... | inl _ = refl
  ... | inr 1≤0 = ⊥-rec (¬-<-zero 1≤0)
  ⅀Idr-preserves-fst (suc A)   (suc m , p) with suc m ≤? 1
  ... | inl sm<1 = ⊥-rec (¬-<-zero (pred-≤-pred sm<1))
  ... | inr _    = cong suc (⅀Idr-preserves-fst A _)

-- ----------------------------------------------------------------------------
-- §5  Associativity, suc-level slice (⅀Assoc-C'-on-inl/-on-inr)
-- ----------------------------------------------------------------------------
--
-- The lexicographic flatten `sumFinBwd (suc A') B (a , b)` lands at the
-- flat index `sum-prefix (suc A') B a + fst b`. Applied to the linearised
-- C-array `⅀Assoc-C'`, the two lemmas below describe how that flatten
-- decomposes:
--
--   `⅀Assoc-C'-on-inl` (left arm)  — when the flat index sits inside
--   the first block (`fst i < B fzero`), `⅀Assoc-C'` reduces to
--   `C fzero i`.
--
--   `⅀Assoc-C'-on-inr` (right arm) — when the flat index has shape
--   `B fzero + fst i` (i.e. sits past the first block), `⅀Assoc-C'`
--   reduces to applying `C ∘ fsuc` to the lex decomposition in the
--   sub-problem on `B ∘ fsuc`.
--
-- Both arms are PUBLIC: consumed by `IExpr.agda` (associativity proof
-- via `joint-C'-on-inj-{l,r}-+`) and `PartialList.agda`. Do not move
-- them into `private`.

private
  opaque
    -- Specialised rephrasings of "fst preservation" for `sumFinFwd`,
    -- packaged for the `inl` arm of `⅀Assoc-C'-on-inl/inr`.
    sumFinFwd-inl-fst : (A' : ℕ) (B : Fin (suc A') → ℕ) (i : Fin (B fzero))
                      (klt : fst i < B fzero + sum A' (B ∘ fsuc))
                      → fst (sumFinFwd (suc A') B (fst i , klt)) ≡ 0
    sumFinFwd-inl-fst A' B (k , k<m) klt with k ≤? B fzero
    ... | inl _ = refl
    ... | inr B≤k = absurd-≤? B≤k k<m

    -- And the corresponding 2nd coord lookup as a ℕ.
    sumFinFwd-inl-snd : (A' : ℕ) (B : Fin (suc A') → ℕ) (i : Fin (B fzero))
                      (klt : fst i < B fzero + sum A' (B ∘ fsuc))
                      → fst (snd (sumFinFwd (suc A') B (fst i , klt))) ≡ fst i
    sumFinFwd-inl-snd A' B (k , k<m) klt with k ≤? B fzero
    ... | inl _ = refl
    ... | inr B≤k = absurd-≤? B≤k k<m

opaque
  -- Inl arm: a "small" flat index `k < B fzero` reduces `⅀Assoc-C'` to
  -- `C fzero` applied to the bridged Fin element.
  ⅀Assoc-C'-on-inl : (A' : ℕ) (B : Fin (suc A') → ℕ)
                     (C : (a : Fin (suc A')) → Fin (B a) → ℕ)
                     (i : Fin (B fzero))
                   → ⅀Assoc-C' (suc A') B C
                       (inj-l-+ (B fzero) (sum A' (B ∘ fsuc)) i)
                   ≡ C fzero i
  ⅀Assoc-C'-on-inl A' B C (k , k<m) with k ≤? B fzero
  ... | inl _   = cong (C fzero) (Fin-fst-≡ refl)
  ... | inr B≤k = absurd-≤? B≤k k<m

  -- Inr arm: a flat index of shape `B fzero + k` lives past the first
  -- block; `sumFinFwd` recurses on `((B fzero + k) ∸ B fzero, _)` which
  -- propositionally equals `(k, _)`. The result is `C ∘ fsuc` applied
  -- to the recursive `sumFinFwd A' (B ∘ fsuc) (k, _)` decomposition.
  ⅀Assoc-C'-on-inr : (A' : ℕ) (B : Fin (suc A') → ℕ)
                     (C : (a : Fin (suc A')) → Fin (B a) → ℕ)
                     (i : Fin (sum A' (B ∘ fsuc)))
                   → ⅀Assoc-C' (suc A') B C
                       (inj-r-+ (B fzero) (sum A' (B ∘ fsuc)) i)
                   ≡ ⅀Assoc-C' A' (B ∘ fsuc) (λ a' → C (fsuc a')) i
  ⅀Assoc-C'-on-inr A' B C (k , klt) with (B fzero + k) ≤? B fzero
  ... | inl B+k<B  = absurd-+-≤? {b = B fzero} {k = k} B+k<B
  ... | inr B≤B+k  =
    cong (λ x → C (fsuc (fst x)) (snd x))
         (cong (sumFinFwd A' (B ∘ fsuc))
               (Fin-fst-≡ ((cong (_∸ B fzero) (+-comm (B fzero) k))
                          ∙ m+n∸n=m (B fzero) k)))

-- ----------------------------------------------------------------------------
-- §6  Associativity, (m+n)-level slice (⅀Assoc-C'-add↑-on-l/-on-r)
-- ----------------------------------------------------------------------------
--
-- (m+n)-level Fubini analogues of `⅀Assoc-C'-on-inl/-on-inr`. The arms
-- match the same pattern at the lifted index:
--
--   `⅀Assoc-C'-add↑-on-l` — a flat `Fin (sum (m + n) B)` index in the
--   m-prefix range reduces to the m-side `⅀Assoc-C'` (with the family
--   reindexed by `inj-l-+ m n`).
--
--   `⅀Assoc-C'-add↑-on-r` — an index of shape
--   `sum m (B ∘ inj-l-+ m n) + k` (with `k < sum n (B ∘ inj-r-+ m n)`)
--   reduces to the n-side `⅀Assoc-C'` (family reindexed by
--   `inj-r-+ m n`).
--
-- Both proceed by induction on `m`:
--   * `m = 0`  — `inj-l-+` is empty / `inj-r-+` is identity (up to
--     `Fin-fst-≡ refl`); the proof is a single `ΣPathP`-bridge.
--   * `m = suc m'` — case-split on `k ≤? B fzero` versus
--     `k ≤? (B ∘ inj-l-+ (suc m') n) fzero`. Three of the four `with`
--     arms are immediate (two impossible via recipe (c); one a direct
--     `ΣPathP` of `Fin`s); the `inr/inr` arm recurses via the IH at
--     `m'` and uses a family-reindex bridge (recipe (d)) to align the
--     two views of `B ∘ fsuc ∘ inj-l-+ m' n` vs
--     `B ∘ inj-l-+ (suc m') n ∘ fsuc`.
--
-- Both lemmas discharge the sum-split side of the `add↑` case of
-- `IExpr-assoc` in `HoTTOperads.Examples.IExpr` and are PUBLIC.

opaque
  unfolding ⅀Assoc-C'-on-inl ⅀Assoc-C'-on-inr

  -- (m+n) left arm. Four `with` arms; only `inr/inr` recurses.
  ⅀Assoc-C'-add↑-on-l :
    (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
    (k : ℕ)
    (kltₗ : k < sum m (B ∘ inj-l-+ m n))
    (klt  : k < sum (m + n) B)
    → ⅀Assoc-C' (m + n) B C (k , klt)
    ≡ ⅀Assoc-C' m (B ∘ inj-l-+ m n) (C ∘ inj-l-+ m n) (k , kltₗ)
  ⅀Assoc-C'-add↑-on-l zero    n B C k kltₗ klt = ⊥-rec (¬-<-zero kltₗ)
  ⅀Assoc-C'-add↑-on-l (suc m') n B C k kltₗ klt
    with k ≤? B fzero | k ≤? (B ∘ inj-l-+ (suc m') n) fzero
  -- (i) inl/inl: both sides reduce to `C fzero (k , …)`. The Fin
  -- elements differ in type (`Fin (B fzero)` vs `Fin (B (inj-l-+ ...))`),
  -- so we build a PathP via ΣPathP using refl on fst and isProp→PathP
  -- on the bound.
  ... | inl k<B0  | inl k<Bₗ0 =
    let
      fz-path : (fzero {k = m' + n}) ≡ inj-l-+ (suc m') n fzero
      fz-path = Fin-fst-≡ refl
      sn-path : PathP (λ j → Fin (B (fz-path j))) (k , k<B0) (k , k<Bₗ0)
      sn-path = ΣPathP (refl , isProp→PathP (λ _ → isProp≤) k<B0 k<Bₗ0)
    in λ i → C (fz-path i) (sn-path i)
  -- (ii) inl/inr: bound contradiction via recipe (c).
  ... | inl k<B0  | inr Bₗ0≤k =
    absurd-≤? Bₗ0≤k
      (subst (k <_)
             (cong B (Fin-fst-≡ {i = fzero}
                                 {j = inj-l-+ (suc m') n fzero} refl))
             k<B0)
  -- (iii) inr/inl: symmetric bound contradiction.
  ... | inr B0≤k  | inl k<Bₗ0 =
    absurd-≤? B0≤k
      (subst (k <_)
             (sym (cong B (Fin-fst-≡ {i = fzero}
                                      {j = inj-l-+ (suc m') n fzero} refl)))
             k<Bₗ0)
  -- (iv) inr/inr — the recursive case. Both LHS and RHS reduce
  -- definitionally to `⅀Assoc-C' (m' + n) (B ∘ fsuc) … (k ∸ B fzero , _)`
  -- (resp. with `Bₗ0` in place of `B fzero`). The IH at `m'` closes the
  -- recursion; a family-reindex bridge (recipe (d)) aligns the two views
  -- of `B ∘ fsuc ∘ inj-l-+ m' n` vs `B ∘ inj-l-+ (suc m') n ∘ fsuc`.
  ... | inr B0≤k  | inr Bₗ0≤k =
    let
      -- (i) Bound propagation: subtract `B fzero` (resp. `Bₗ0`) from
      -- both the LHS bound and the RHS bound, using `∸-<-lemma`.
      klt-rec  : k ∸ B fzero < sum (m' + n) (B ∘ fsuc)
      klt-rec  = ∸-<-lemma (B fzero) (sum (m' + n) (B ∘ fsuc)) k klt B0≤k
      kltₗ-rec : k ∸ (B ∘ inj-l-+ (suc m') n) fzero
               < sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)
      kltₗ-rec = ∸-<-lemma ((B ∘ inj-l-+ (suc m') n) fzero)
                            (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)) k kltₗ Bₗ0≤k
      -- (ii) ∸-bridge: `k ∸ B fzero` and `k ∸ Bₗ0` are propositionally
      -- equal via `Fin-fst-≡ refl` on the index.
      ∸-bridge : k ∸ B fzero ≡ k ∸ (B ∘ inj-l-+ (suc m') n) fzero
      ∸-bridge = cong (k ∸_) (cong B (Fin-fst-≡ {i = fzero}
                                                  {j = inj-l-+ (suc m') n fzero} refl))
      -- Bridge bound proof for IH's right input.
      kltₗ-rec' : k ∸ B fzero < sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n)
      kltₗ-rec' = subst (k ∸ B fzero <_)
                         (cong (sum m')
                               (funExt λ a → cong B (Fin-fst-≡
                                 {i = inj-l-+ (suc m') n (fsuc a)}
                                 {j = fsuc (inj-l-+ m' n a)} refl)))
                         (subst (_< sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc))
                                (sym ∸-bridge)
                                kltₗ-rec)
      -- (iii) IH application. With both arms in `inr`, both `⅀Assoc-C'`
      -- sides reduce definitionally through `sumFinFwd`'s case-split.
      IH : ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
             (k ∸ B fzero , klt-rec)
         ≡ ⅀Assoc-C' m' ((B ∘ fsuc) ∘ inj-l-+ m' n)
                          ((λ a' → C (fsuc a')) ∘ inj-l-+ m' n)
                          (k ∸ B fzero , kltₗ-rec')
      IH = ⅀Assoc-C'-add↑-on-l m' n (B ∘ fsuc) (λ a' → C (fsuc a'))
                                 (k ∸ B fzero) kltₗ-rec' klt-rec
      -- (iv) Family-reindex bridge (recipe (d)). The two endpoints
      -- live in different `Fin (sum m' …)` types — `(B ∘ fsuc) ∘
      -- inj-l-+ m' n` versus `(B ∘ inj-l-+ (suc m') n) ∘ fsuc`. The
      -- third Σ-pair argument needs a heterogeneous PathP, not a
      -- `Fin-fst-≡`.
      B-fam-path : (a : Fin m')
                 → (B ∘ fsuc) (inj-l-+ m' n a) ≡ (B ∘ inj-l-+ (suc m') n) (fsuc a)
      B-fam-path a = cong B (Fin-fst-≡ {i = fsuc (inj-l-+ m' n a)}
                                          {j = inj-l-+ (suc m') n (fsuc a)} refl)
      Σ-elem : PathP (λ i → Fin (sum m' (λ a → B-fam-path a i)))
                     (k ∸ B fzero , kltₗ-rec')
                     (k ∸ (B ∘ inj-l-+ (suc m') n) fzero , kltₗ-rec)
      Σ-elem = ΣPathP {A = λ _ → ℕ}
                       {B = λ i k' → k' < sum m' (λ a → B-fam-path a i)}
                       (∸-bridge , isProp→PathP (λ _ → isProp≤) kltₗ-rec' kltₗ-rec)
      family-bridge :
          ⅀Assoc-C' m' ((B ∘ fsuc) ∘ inj-l-+ m' n)
                       ((λ a' → C (fsuc a')) ∘ inj-l-+ m' n)
                       (k ∸ B fzero , kltₗ-rec')
        ≡ ⅀Assoc-C' m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)
                       ((C ∘ inj-l-+ (suc m') n) ∘ fsuc)
                       (k ∸ (B ∘ inj-l-+ (suc m') n) fzero , kltₗ-rec)
      family-bridge i =
        ⅀Assoc-C' m'
          (λ a → B-fam-path a i)
          (λ a b → C (Fin-fst-≡ {i = fsuc (inj-l-+ m' n a)}
                                  {j = inj-l-+ (suc m') n (fsuc a)} refl i)
                       b)
          (Σ-elem i)
    in IH ∙ family-bridge

  -- (m+n) right arm. Two cases on `m`; the `suc m'` case bridges the
  -- LHS index through `⅀Assoc-C'-on-inr` (§5) and recurses via the IH.
  ⅀Assoc-C'-add↑-on-r :
    (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
    (k : ℕ)
    (kltᵣ : k < sum n (B ∘ inj-r-+ m n))
    (klt  : sum m (B ∘ inj-l-+ m n) + k < sum (m + n) B)
    → ⅀Assoc-C' (m + n) B C (sum m (B ∘ inj-l-+ m n) + k , klt)
    ≡ ⅀Assoc-C' n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n) (k , kltᵣ)
  -- `m = 0`: `inj-l-+ 0 n` is empty so `sum 0 (B ∘ inj-l-+ 0 n) = 0`,
  -- and `inj-r-+ 0 n` is identity up to `Fin-fst-≡ refl`. The two
  -- endpoint families are `B` and `B ∘ inj-r-+ 0 n` — same function
  -- pointwise; the Σ-pair bound proofs live in different `Fin` types,
  -- so the third argument is a heterogeneous PathP via `ΣPathP`.
  ⅀Assoc-C'-add↑-on-r zero    n B C k kltᵣ klt =
    let
      B-fam-path : (a : Fin n) → B a ≡ (B ∘ inj-r-+ zero n) a
      B-fam-path a = cong B (Fin-fst-≡ {i = a} {j = inj-r-+ zero n a} refl)
      Σ-elem : PathP (λ i → Fin (sum n (λ a → B-fam-path a i)))
                     (k , klt) (k , kltᵣ)
      Σ-elem = ΣPathP {A = λ _ → ℕ}
                       {B = λ i k' → k' < sum n (λ a → B-fam-path a i)}
                       (refl , isProp→PathP (λ _ → isProp≤) klt kltᵣ)
    in λ i → ⅀Assoc-C' n (λ a → B-fam-path a i)
                         (λ a b → C (Fin-fst-≡ {i = a} {j = inj-r-+ zero n a} refl i) b)
                         (Σ-elem i)
  -- `m = suc m'`: the LHS index `sum (suc m') (B ∘ inj-l-+ (suc m') n)
  -- + k` does NOT reduce definitionally to a `B fzero + …`-form, so
  -- `sumFinFwd`'s top-level `with` doesn't fire. We explicitly bridge
  -- the index (`index-bridge`), apply `⅀Assoc-C'-on-inr` (§5), recurse
  -- via the IH at `m'`, then bridge the n-side family-reindexing.
  ⅀Assoc-C'-add↑-on-r (suc m') n B C k kltᵣ klt =
    let
      Bₗ-fzero-eq : B fzero ≡ (B ∘ inj-l-+ (suc m') n) fzero
      Bₗ-fzero-eq = cong B (Fin-fst-≡ {i = fzero} {j = inj-l-+ (suc m') n fzero} refl)

      -- (i) index-bridge: rearrange `sum (suc m') (B ∘ inj-l-+ (suc m') n)
      -- + k` into `B fzero + (sum m' … + k)` via `sym Bₗ-fzero-eq` and
      -- `sym +-assoc`.
      index-bridge : sum (suc m') (B ∘ inj-l-+ (suc m') n) + k
                   ≡ B fzero + (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) + k)
      index-bridge = cong (_+ k) (cong (_+ sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc))
                                        (sym Bₗ-fzero-eq))
                    ∙ sym (+-assoc (B fzero) (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)) k)

      full-klt : B fzero + (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) + k)
               < B fzero + sum (m' + n) (B ∘ fsuc)
      full-klt = subst (_< B fzero + sum (m' + n) (B ∘ fsuc)) index-bridge klt

      klt-inner : sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) + k < sum (m' + n) (B ∘ fsuc)
      klt-inner = <-k+-cancel {k = B fzero} full-klt

      -- (ii) family-reindex bridge on the left half (recipe (d)).
      sum-prefix-fam-path : (a : Fin m')
                          → (B ∘ inj-l-+ (suc m') n) (fsuc a) ≡ (B ∘ fsuc) (inj-l-+ m' n a)
      sum-prefix-fam-path a = cong B (Fin-fst-≡ {i = inj-l-+ (suc m') n (fsuc a)}
                                                   {j = fsuc (inj-l-+ m' n a)} refl)

      klt-inner' : sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k < sum (m' + n) (B ∘ fsuc)
      klt-inner' = subst (_< sum (m' + n) (B ∘ fsuc))
                          (cong (_+ k) (cong (sum m') (funExt sum-prefix-fam-path)))
                          klt-inner

      -- (ii') family-reindex bridge on the right half.
      Bᵣ-fam-path : (a : Fin n)
                  → (B ∘ inj-r-+ (suc m') n) a ≡ (B ∘ fsuc) (inj-r-+ m' n a)
      Bᵣ-fam-path a = cong B (Fin-fst-≡ {i = inj-r-+ (suc m') n a}
                                          {j = fsuc (inj-r-+ m' n a)} refl)

      kltᵣ' : k < sum n ((B ∘ fsuc) ∘ inj-r-+ m' n)
      kltᵣ' = subst (k <_) (cong (sum n) (funExt Bᵣ-fam-path)) kltᵣ

      -- (iii) IH at m'.
      IH : ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
             (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k , klt-inner')
         ≡ ⅀Assoc-C' n ((B ∘ fsuc) ∘ inj-r-+ m' n)
                          ((λ a' → C (fsuc a')) ∘ inj-r-+ m' n) (k , kltᵣ')
      IH = ⅀Assoc-C'-add↑-on-r m' n (B ∘ fsuc) (λ a' → C (fsuc a')) k kltᵣ' klt-inner'

      -- (iv) Three path-valued helpers chaining LHS → IH → RHS.
      lhs-step : ⅀Assoc-C' (suc m' + n) B C
                   (sum (suc m') (B ∘ inj-l-+ (suc m') n) + k , klt)
               ≡ ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                              (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) + k , klt-inner)
      lhs-step =
          cong (⅀Assoc-C' (suc m' + n) B C)
               (Fin-fst-≡ {i = (sum (suc m') (B ∘ inj-l-+ (suc m') n) + k , klt)}
                          {j = (B fzero + (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) + k)
                               , <-k+ {k = B fzero} klt-inner)}
                          index-bridge)
        ∙ ⅀Assoc-C'-on-inr (m' + n) B C
                            (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) + k , klt-inner)

      -- Pre-IH-bridge: align the family from `(B ∘ inj-l-+ (suc m') n)
      -- ∘ fsuc` to `(B ∘ fsuc) ∘ inj-l-+ m' n` on the left half.
      pre-IH-bridge :
          ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                       (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) + k , klt-inner)
        ≡ ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                       (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k , klt-inner')
      pre-IH-bridge = cong (⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a')))
                            (Fin-fst-≡ (cong (_+ k) (cong (sum m')
                                                     (funExt sum-prefix-fam-path))))

      -- Post-IH-bridge: align the n-side family from `(B ∘ fsuc) ∘
      -- inj-r-+ m' n` to `B ∘ inj-r-+ (suc m') n` via `Bᵣ-fam-path`.
      post-IH-bridge :
          ⅀Assoc-C' n ((B ∘ fsuc) ∘ inj-r-+ m' n)
                       ((λ a' → C (fsuc a')) ∘ inj-r-+ m' n) (k , kltᵣ')
        ≡ ⅀Assoc-C' n (B ∘ inj-r-+ (suc m') n) (C ∘ inj-r-+ (suc m') n) (k , kltᵣ)
      post-IH-bridge i =
        ⅀Assoc-C' n
          (λ a → Bᵣ-fam-path a (~ i))
          (λ a b → C (Fin-fst-≡ {i = inj-r-+ (suc m') n a}
                                  {j = fsuc (inj-r-+ m' n a)} refl (~ i))
                       b)
          (ΣPathP {A = λ _ → ℕ}
                   {B = λ j k' → k' < sum n (λ a → Bᵣ-fam-path a (~ j))}
                   (refl , isProp→PathP (λ _ → isProp≤) kltᵣ' kltᵣ) i)
    in lhs-step ∙ pre-IH-bridge ∙ IH ∙ post-IH-bridge

-- ----------------------------------------------------------------------------
-- §7  Fubini identity: `sum-prefix-ℕ-PathP`, `fubini`
-- ----------------------------------------------------------------------------
--
-- The lexicographic flatten `sumFinBwd A B (a , b)` lands at the flat
-- index `sum-prefix A B a + fst b`. Applying `sum-prefix-ℕ` of the
-- linearised `⅀Assoc-C'`-array to that index splits as the "full
-- first-block" portion (a complete `sum (B a') (C a')` for each
-- `a' < a`) plus the "partial b" portion (a prefix sum of `C a`).
-- This is `fubini`, proved by induction on `A` using §5 and §6.

opaque
  -- Transport of `sum-prefix-ℕ` along paths on both the bound and the
  -- function: by joint continuity, this is just `λ i → sum-prefix-ℕ
  -- (p i) (q i) k`.
  sum-prefix-ℕ-PathP : {X Y : ℕ} (p : X ≡ Y) {f : Fin X → ℕ} {g : Fin Y → ℕ}
                     → PathP (λ i → Fin (p i) → ℕ) f g
                     → (k : ℕ)
                     → sum-prefix-ℕ X f k ≡ sum-prefix-ℕ Y g k
  sum-prefix-ℕ-PathP p q k i = sum-prefix-ℕ (p i) (q i) k

  -- Fubini identity (recipe (b)). Induction on `A`:
  --   * `zero` — impossible (bound is `Fin 0`).
  --   * `(suc A', zero)` — LHS reduces to `sum-prefix-ℕ (B fzero + …)`
  --     over `⅀Assoc-C'` at index `fst b < B fzero`. Apply
  --     `sum-prefix-ℕ-l`, then `⅀Assoc-C'-on-inl` (§5).
  --   * `(suc A', suc k)` — reassociate the index, apply
  --     `sum-prefix-ℕ-r` to split off the first block, simplify the
  --     two halves via `⅀Assoc-C'-on-inl`/`-on-inr` (§5) plus the IH,
  --     then reassociate to bridge to the RHS.
  fubini : (A : ℕ) (B : Fin A → ℕ) (C : (a : Fin A) → Fin (B a) → ℕ)
         → (a : Fin A) (b : Fin (B a))
         → sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C)
                        (sum-prefix-ℕ A B (fst a) + fst b)
         ≡ sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a)
         + sum-prefix-ℕ (B a) (C a) (fst b)
  fubini zero    B C (_     , p) b = ⊥-rec (¬-<-zero p)
  fubini (suc A') B C (zero  , p) b =
    -- Zero clause. `sum-prefix-ℕ (suc A') B 0 = 0`, so the LHS
    -- collapses to `sum-prefix-ℕ (B fzero + sum A' (B ∘ fsuc))
    -- (⅀Assoc-C') (fst b)` with `fst b < B fzero` (bridged via
    -- `Fin-fst-≡ refl`).
      sum-prefix-ℕ-l (B fzero) (sum A' (B ∘ fsuc))
                     (⅀Assoc-C' (suc A') B C)
                     (fst b)
                     (<-weaken (subst (fst b <_) (cong B (Fin-fst-≡ refl)) (snd b)))
    ∙ sum-prefix-ℕ-cong (B fzero) (⅀Assoc-C'-on-inl A' B C) (fst b)
    ∙ sum-prefix-ℕ-PathP (cong B fzero≡a) (λ i → C (fzero≡a i)) (fst b)
    where
      fzero≡a : _≡_ {A = Fin (suc A')} fzero (zero , p)
      fzero≡a = Fin-fst-≡ refl
  fubini (suc A') B C (suc k , p) b =
    -- Suc clause. LHS = sum-prefix-ℕ (B fzero + sum A' (B ∘ fsuc))
    -- (⅀Assoc-C') (B fzero + sum-prefix-ℕ A' (B ∘ fsuc) k + fst b).
    -- Reassociate the index, then apply `sum-prefix-ℕ-r`.
      cong (sum-prefix-ℕ (B fzero + sum A' (B ∘ fsuc)) (⅀Assoc-C' (suc A') B C))
           (sym (+-assoc (B fzero) (sum-prefix-ℕ A' (B ∘ fsuc) k) (fst b)))
    ∙ sum-prefix-ℕ-r (B fzero) (sum A' (B ∘ fsuc))
                      (⅀Assoc-C' (suc A') B C)
                      (sum-prefix-ℕ A' (B ∘ fsuc) k + fst b)
                      bound-ok
    -- First summand: `⅀Assoc-C'-on-inl` + `sum-cong`. Second summand:
    -- `⅀Assoc-C'-on-inr` + `sum-prefix-ℕ-cong`, then the IH at `A'`.
    ∙ cong₂ _+_
          (sum-cong (B fzero) (⅀Assoc-C'-on-inl A' B C))
          ( sum-prefix-ℕ-cong (sum A' (B ∘ fsuc))
                                (⅀Assoc-C'-on-inr A' B C)
                                (sum-prefix-ℕ A' (B ∘ fsuc) k + fst b)
          ∙ fubini A' (B ∘ fsuc) (λ a' → C (fsuc a')) (k , pred-≤-pred p) b' )
    -- Reassociate, then bridge `b` (lives in `Fin (B (suc k, p))`) back
    -- to `b'` (lives in `Fin ((B ∘ fsuc) (k, pred-≤-pred p))`).
    ∙ +-assoc (sum (B fzero) (C fzero))
              (sum-prefix-ℕ A' (λ a' → sum (B (fsuc a')) (C (fsuc a'))) k)
              (sum-prefix-ℕ (B (fsuc (k , pred-≤-pred p)))
                            (C (fsuc (k , pred-≤-pred p))) (fst b'))
    ∙ cong (λ x → sum (B fzero) (C fzero)
                + sum-prefix-ℕ A' (λ a' → sum (B (fsuc a')) (C (fsuc a'))) k
                + x)
           (sum-prefix-ℕ-PathP (cong B (sym fsuc-eq))
                                (λ i → C (sym fsuc-eq i)) (fst b))
    where
      fsuc-eq : _≡_ {A = Fin (suc A')} (suc k , p) (fsuc (k , pred-≤-pred p))
      fsuc-eq = Fin-fst-≡ refl

      -- `b` bridged from `Fin (B (suc k, p))` to `Fin ((B ∘ fsuc) (k,
      -- pred-≤-pred p))`. Kept transparent: the recursive `fubini`
      -- call below depends on `fst b' = fst b` reducing definitionally
      -- (via Cubical's `transp` on Σ commuting with `fst`), which
      -- requires Agda to see `b'`'s `subst`-body.
      b' : Fin ((B ∘ fsuc) (k , pred-≤-pred p))
      b' = subst (λ x → Fin (B x)) fsuc-eq b

      -- `fst b' ≡ fst b` (substitution along a path-of-ℕ preserves
      -- `fst` on `Fin`).
      -- NOTE: We keep this local helper rather than importing
      -- `transport-Fin-fst` from `Prelude.Nat`. Reason: the call site
      -- applies the lemma to `subst Fin q b`, not `transport (cong
      -- Fin q) b`. In Cubical, `subst Fin q b` is `transp (λ i →
      -- Fin (q i)) i0 b`, which is *not* definitionally `transport
      -- (cong Fin q) b`. Bridging the two would cost a `substRefl`
      -- /`transportRefl` step for no real gain.
      fst-b'≡fst-b : fst b' ≡ fst b
      fst-b'≡fst-b = fst-subst-Fin (cong B fsuc-eq) b
        where
          fst-subst-Fin : {a b : ℕ} (q : a ≡ b) (x : Fin a)
                        → fst (subst Fin q x) ≡ fst x
          fst-subst-Fin {a} = J (λ b q → (x : Fin a) → fst (subst Fin q x) ≡ fst x)
                                (λ x → cong fst (substRefl {B = Fin} x))

      -- Bound for `sum-prefix-ℕ-r`: a strict version follows from
      -- `sum-prefix-bound`, then weaken to `≤` and bridge `fst b'` to
      -- `fst b`.
      bound-strict : sum-prefix-ℕ A' (B ∘ fsuc) k + fst b' < sum A' (B ∘ fsuc)
      bound-strict =
        subst (λ x → x + fst b' < sum A' (B ∘ fsuc))
              (sum-prefix-≡ A' (B ∘ fsuc) (k , pred-≤-pred p))
              (sum-prefix-bound A' (B ∘ fsuc) (k , pred-≤-pred p) (fst b') (snd b'))
        where open import HoTTOperads.Prelude.Nat using (sum-prefix-bound)

      bound-ok : sum-prefix-ℕ A' (B ∘ fsuc) k + fst b ≤ sum A' (B ∘ fsuc)
      bound-ok = subst (λ x → sum-prefix-ℕ A' (B ∘ fsuc) k + x ≤ sum A' (B ∘ fsuc))
                       fst-b'≡fst-b
                       (<-weaken bound-strict)

-- ----------------------------------------------------------------------------
-- §8  Forward fst-preservation via the inverse trace
-- ----------------------------------------------------------------------------
--
-- We discharge `⅀Assoc-preserves-fst` (the third coherence's hypothesis
-- for recipe (a)) by first establishing the INVERSE form
-- `⅀Assoc-preserves-fst-INV`: `fst (invEq (⅀Assoc≃ A B C) k) ≡ fst k`.
-- The forward form then follows via `retEq`.
--
-- The inverse trace is built from seven `step`-paths chained together:
--   step1  Bridge both `sum-prefix` to `sum-prefix-ℕ` (via
--          `sum-prefix-≡` on each side).
--   step2  Reassociate `X + (Y + Z) ≡ (X + Y) + Z`.
--   step3  Apply `sym (fubini)` to fold the LHS back into a
--          `sum-prefix-ℕ` over `⅀Assoc-C'`.
--   step4  Bridge `sum-prefix-ℕ A B (fst a)` back to `sum-prefix A B a`.
--   step5  Bridge `sum-prefix-ℕ (sum A B) (⅀Assoc-C') (x + fst b)` to
--          `sum-prefix (sum A B) (⅀Assoc-C') (sumFinBwd A B (a , b))`.
--   step6  Apply `sumFinBwd-Fwd A B ab` to simplify the inner
--          `sumFinBwd A B (sumFinFwd A B ab)` to `ab`.
--   step7  Apply `sumFinBwd-Fwd (sum A B) (⅀Assoc-C') k` to close.

-- The sanity-check module below pins the *exact* structural shape of
-- `fst (invEq (⅀Assoc≃ A B C) k)` that `⅀Assoc-preserves-fst-INV`
-- relies on.
private
  module _ (A : ℕ) (B : Fin A → ℕ) (C : (a : Fin A) → Fin (B a) → ℕ)
           (k : Fin (sum (sum A B) (⅀Assoc-C' A B C))) where
    abc = sumFinFwd (sum A B) (⅀Assoc-C' A B C) k
    ab  = fst abc
    c   = snd abc
    ab' = sumFinFwd A B ab
    a   = fst ab'
    b   = snd ab'

    -- The fst of `invEq (⅀Assoc≃ A B C) k` is literally the seven-
    -- term expression below — every step of `⅀Assoc-preserves-fst-INV`
    -- chains paths starting from this shape.
    _ : fst (invEq (⅀Assoc≃ A B C) k)
      ≡ sum-prefix A (λ a' → sum (B a') (C a')) a
      + (sum-prefix (B a) (C a) b + fst c)
    _ = refl

opaque
  -- Inverse direction. Definitionally, `fst (invEq ⅀Assoc≃ k) =
  -- sum-prefix A (..) a + (sum-prefix (B a) (C a) b + fst c)` (see the
  -- sanity-check above). Chain seven `step`-paths to close.
  ⅀Assoc-preserves-fst-INV : (A : ℕ) (B : Fin A → ℕ)
                             (C : (a : Fin A) → Fin (B a) → ℕ)
                           → (k : Fin (sum (sum A B) (⅀Assoc-C' A B C)))
                           → fst (invEq (⅀Assoc≃ A B C) k) ≡ fst k
  ⅀Assoc-preserves-fst-INV A B C k =
    let abc = sumFinFwd (sum A B) (⅀Assoc-C' A B C) k
        ab  = fst abc
        c   = snd abc
        ab' = sumFinFwd A B ab
        a   = fst ab'
        b   = snd ab'
        -- step1: bridge both `sum-prefix` to `sum-prefix-ℕ`.
        step1 : sum-prefix A (λ a' → sum (B a') (C a')) a + (sum-prefix (B a) (C a) b + fst c)
              ≡ sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + (sum-prefix-ℕ (B a) (C a) (fst b) + fst c)
        step1 = cong₂ _+_ (sum-prefix-≡ A _ a)
                            (cong (_+ fst c) (sum-prefix-≡ (B a) (C a) b))
        -- step2: reassociate `X + (Y + Z) ≡ (X + Y) + Z`.
        step2 : sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + (sum-prefix-ℕ (B a) (C a) (fst b) + fst c)
              ≡ sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + sum-prefix-ℕ (B a) (C a) (fst b) + fst c
        step2 = +-assoc (sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a))
                        (sum-prefix-ℕ (B a) (C a) (fst b))
                        (fst c)
        -- step3: apply `sym (fubini)` — fubini's RHS matches step2's RHS.
        step3 : sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + sum-prefix-ℕ (B a) (C a) (fst b) + fst c
              ≡ sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix-ℕ A B (fst a) + fst b) + fst c
        step3 = cong (_+ fst c) (sym (fubini A B C a b))
        -- step4: bridge `sum-prefix-ℕ A B (fst a)` back to `sum-prefix A B a`.
        step4 : sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix-ℕ A B (fst a) + fst b) + fst c
              ≡ sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix A B a + fst b) + fst c
        step4 = cong (λ x → sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (x + fst b) + fst c)
                     (sym (sum-prefix-≡ A B a))
        -- step5: `sum-prefix A B a + fst b ≡ fst (sumFinBwd A B (a , b))`
        --        definitionally; bridge `sum-prefix-ℕ` to `sum-prefix`.
        step5 : sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix A B a + fst b) + fst c
              ≡ sum-prefix (sum A B) (⅀Assoc-C' A B C) (sumFinBwd A B (a , b)) + fst c
        step5 = cong (_+ fst c) (sym (sum-prefix-≡ (sum A B) (⅀Assoc-C' A B C) (sumFinBwd A B (a , b))))
        -- step6: `sumFinBwd-Fwd A B ab` — applied to `(a , b) = sumFinFwd A B ab`.
        step6 : sum-prefix (sum A B) (⅀Assoc-C' A B C) (sumFinBwd A B (a , b)) + fst c
              ≡ sum-prefix (sum A B) (⅀Assoc-C' A B C) ab + fst c
        step6 = cong (λ x → sum-prefix (sum A B) (⅀Assoc-C' A B C) x + fst c)
                     (sumFinBwd-Fwd A B ab)
        -- step7: by definition of `sumFinBwd`, this is `fst (sumFinBwd
        --        (sum A B) (⅀Assoc-C' A B C) (ab , c))`; `sumFinBwd-Fwd`
        --        on the outer level closes.
        step7 : sum-prefix (sum A B) (⅀Assoc-C' A B C) ab + fst c
              ≡ fst k
        step7 = cong fst (sumFinBwd-Fwd (sum A B) (⅀Assoc-C' A B C) k)
    in step1 ∙ step2 ∙ step3 ∙ step4 ∙ step5 ∙ step6 ∙ step7

  -- Forward direction follows via `retEq`.
  ⅀Assoc-preserves-fst : (A : ℕ) (B : Fin A → ℕ)
                         (C : (a : Fin A) → Fin (B a) → ℕ)
                         (k : Fin (sum A (λ a → sum (B a) (C a))))
                       → fst (equivFun (⅀Assoc≃ A B C) k) ≡ fst k
  ⅀Assoc-preserves-fst A B C k =
      sym (⅀Assoc-preserves-fst-INV A B C (equivFun (⅀Assoc≃ A B C) k))
    ∙ cong fst (retEq (⅀Assoc≃ A B C) k)

-- ----------------------------------------------------------------------------
-- §9  Universe assembly: `𝓝-coh`, `𝓝`
-- ----------------------------------------------------------------------------
--
-- Each of the three coherences is `coh-from-fst` applied to the
-- corresponding `…-preserves-fst` lemma. The chosen path argument is
-- `+-zero A` (Idl), `sum-idr A` (Idr), and `NatInj (⅀Assoc≃ A B C)`
-- (Assoc) — though by `isSetℕ` the choice is immaterial.

𝓝-coh : UniverseCoh 𝓝-base
UniverseCoh.⟦⅀Idl⟧   𝓝-coh A     = coh-from-fst (⅀Idl≃ A)         (+-zero A)   (⅀Idl-preserves-fst A)
UniverseCoh.⟦⅀Idr⟧   𝓝-coh A     = coh-from-fst (⅀Idr≃ A)         (sum-idr A) (⅀Idr-preserves-fst A)
UniverseCoh.⟦⅀Assoc⟧ 𝓝-coh A B C = coh-from-fst (⅀Assoc≃ A B C)   (NatInj (⅀Assoc≃ A B C))
                                                (⅀Assoc-preserves-fst A B C)

-- The 𝓝 universe of totally-ordered finite sets.
𝓝 : Universe ℓ-zero ℓ-zero
Universe.base 𝓝 = 𝓝-base
Universe.coh  𝓝 = 𝓝-coh
