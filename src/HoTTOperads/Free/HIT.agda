{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Free.HIT
--
-- The free 𝒰-operad on a family K : Code → Type, presented as a higher
-- inductive family `FreeOps K : Code → Type`. Operadic composition is `graft`,
-- and we discharge the three coherence laws (left identity, right identity,
-- associativity) constructively in Cubical Agda. The construction follows
-- FreeOperad.tex §9 (lines 87-118); the recipe below names the patterns used
-- pervasively in the associativity proof.
--
-- ## File layout
--
--   §2  The HIT FreeOps (constructors `leaf`, `node`, `set`).
--   §3  The composition `graft` (recursive on the first tree).
--   §4  Substitution toolkit
--         ⅀-subst-path, graft-subst-fst, graft-subst-snd.
--       Push `subst (FreeOps K)` across an outer `graft`.
--   §5  Reduction toolkit
--         adj-coh, Assoc-cont, Assoc-cont-at-pair, step-Assoc-on-pair,
--         transp-⅀AssocD-pair, transp-⅀IdlD, transp-⅀-subst-path.
--       Generic statements about how transports along the universe paths
--       `Inj (⅀Assoc≃ A B C)`, `⅀AssocD A B C`, and `⅀IdlD X` act on a
--       *canonical pair* input `invEq (⟦⅀⟧ A …) (a , z)`. Every site in §8
--       that previously inlined a ~30-line `congFunct`/`substComposite` chain
--       now invokes one of these.
--   §6  Left identity `graft-idl`.
--   §7  Right identity `graft-idr` (cases: leaf | node | set).
--   §8  Associativity `graft-assoc` (cases: leaf | node | set).
--   §9  Operad assembly: `isSetFreeOps`, `FreeOperad`.
--
-- ## The five-step Recipe used in graft-assoc
--
-- Each transport-along-`⅀AssocD`-on-canonical-pair site decomposes as:
--
--   (a) `Assoc-cont A B C p` — the explicit Σ-shuffle that `equivFun (⅀Assoc≃
--       A B C)` unfolds to (by `compEquiv` reducing definitionally on Σ).
--   (b) `Assoc-cont-at-pair` — `equivFun (⅀Assoc≃) (invEq ⟦⅀⟧ p) ≡ Assoc-cont
--       p`, by `cong (Assoc-cont _) (secEq …)`.
--   (c) `step-Assoc-on-pair` — `transport (cong El (Inj (⅀Assoc≃ A B C))) ∘
--       invEq ⟦⅀⟧ ≡ Assoc-cont A B C`, via `⟦⅀Assoc⟧` + `uaβ` + (b).
--   (d) `transp-⅀AssocD-pair` — the analogous fact for the whole `⅀AssocD`
--       path (which is `Inj (⅀Assoc≃) ∙ cong (⅀ _) C'-eq`), built by composing
--       (c) with a `⟦⅀⟧-natural-snd` step and an internal `adj-coh`-driven
--       `c-restore` that recovers the canonical `snd` component.
--   (e) `adj-coh` — adjunction coherence for an arbitrary equivalence,
--       used inside (d) to relate `funExt⁻ C'-eq` transports back to `secEq`.
-- ============================================================================
module HoTTOperads.Free.HIT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (homotopyNatural)
open import Cubical.Foundations.HLevels using (isOfHLevelPathP')
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.GroupoidLaws using (lCancel ; rUnit ; lUnit ; assoc ; congFunct ; symDistr)
open import Cubical.Foundations.Path using (isProp→SquareP)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; uaInvEquiv ; pathToEquiv ; pathToEquivRefl ; ua-pathToEquiv ; pathToEquiv-ua ; uaCompEquiv ; EquivJ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; Σ ; ΣPathP)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-snd ; Σ-cong-equiv-fst ; Σ-assoc-≃)
open import Cubical.Data.Unit using (tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Derived
open import HoTTOperads.Universe.IRDerived
open import HoTTOperads.Operad.Base

private
  variable
    ℓc ℓe ℓk : Level

module _ {𝒰 : Universe ℓc ℓe} where
  open Universe 𝒰

  -- ============================================================================
  -- §2  The free operad as a HIT
  --
  -- `FreeOps K A` is the type of K-labelled trees with leaves indexed by `El 𝜏`
  -- and indexed branching by `⅀`-pairs, quotiented by the `set` truncation that
  -- forces every fibre to be an h-set. The three constructors match the
  -- presentation in FreeOperad.tex §9.
  -- ============================================================================
  data FreeOps (K : Code → Type ℓk) : Code → Type (ℓ-max (ℓ-max ℓc ℓe) ℓk) where
    leaf : FreeOps K 𝜏
    node : (A : Code) (B : El A → Code)
         → K A → ((a : El A) → FreeOps K (B a))
         → FreeOps K (⅀ A B)
    set  : (A : Code) (x y : FreeOps K A) (p q : x ≡ y) → p ≡ q

  -- ============================================================================
  -- §3  Graft (the operadic composition)
  --
  -- `graft K A C t f` substitutes the subtrees `f : ∀ a, FreeOps K (C a)` at
  -- each leaf of `t : FreeOps K A`. On `leaf` we take the unique input via
  -- `⅀IdlD`; on a `node A B k ts` we recurse and then `subst` along
  -- `⅀AssocD A B C` to bring the indices into the operadic form.
  -- ============================================================================
  opaque
    -- Distribute `subst (FreeOps K) (cong (⅀ A) q)` over a `node`: the outer
    -- subst splits as a `node` whose per-fibre subtrees are themselves substed
    -- along the corresponding `funExt⁻ q a`. Proved by `J` on `q`: at `q = refl`
    -- both sides reduce to `node A B₁ k ts` modulo `substRefl`.
    subst-cong-⅀-node : (K : Code → Type ℓk) (A : Code)
                        {B₁ B₂ : El A → Code} (q : B₁ ≡ B₂)
                        (k : K A) (ts : (a : El A) → FreeOps K (B₁ a))
                      → subst (FreeOps K) (cong (⅀ A) q) (node A B₁ k ts)
                      ≡ node A B₂ k (λ a → subst (FreeOps K) (funExt⁻ q a) (ts a))
    subst-cong-⅀-node K A {B₁} =
      J (λ B₂ q →
           (k : K A) (ts : (a : El A) → FreeOps K (B₁ a))
         → subst (FreeOps K) (cong (⅀ A) q) (node A B₁ k ts)
         ≡ node A B₂ k (λ a → subst (FreeOps K) (funExt⁻ q a) (ts a)))
        (λ k ts →
           substRefl {B = FreeOps K} (node A B₁ k ts)
           ∙ cong (node A B₁ k)
                  (funExt (λ a → sym (substRefl {B = FreeOps K} (ts a)))))

  graft : (K : Code → Type ℓk) (A : Code) (C : El A → Code)
        → FreeOps K A
        → ((a : El A) → FreeOps K (C a))
        → FreeOps K (⅀ A C)
  graft K .(𝜏) C leaf ts =
    subst (FreeOps K) (⅀IdlD 𝒰 C) (ts (invEq ⟦𝜏⟧ tt))
  graft K .(⅀ A B) C (node A B k ts) tss =
    subst (FreeOps K) (⅀AssocD 𝒰 A B C)
          (node A (λ a → ⅀ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) k
                (λ a → graft K (B a)
                              (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))
                              (ts a)
                              (λ b → tss (invEq (⟦⅀⟧ A B) (a , b)))))
  graft K A C (set .(A) x y p q i j) tss =
    set (⅀ A C) (graft K A C x tss) (graft K A C y tss)
        (λ k → graft K A C (p k) tss)
        (λ k → graft K A C (q k) tss) i j

  -- ============================================================================
  -- §4  Substitution toolkit
  --
  -- Three lemmas for pushing a `subst (FreeOps K) _` across an outer `graft`:
  --   * `⅀-subst-path p C` is the cubical index path along which the LHS-input
  --     of `graft` reindexes.
  --   * `graft-subst-fst`  pushes the subst over the first (tree) argument.
  --   * `graft-subst-snd`  pushes it over the second (per-fibre) function.
  -- All three are used in §8.
  -- ============================================================================

  -- The cubical index path along which the *first* argument of `graft` reindexes
  -- when its tree is substed along `p : A ≡ A'`. Built by varying the outer code
  -- along `p i` and the per-fibre code along a partial `El`-transport that is the
  -- identity at `i = 1` (so the path lands at `⅀ A' C` definitionally).
  ⅀-subst-path : {A A' : Code} (p : A ≡ A') (C : El A' → Code)
               → ⅀ A (λ a → C (transport (cong El p) a)) ≡ ⅀ A' C
  ⅀-subst-path p C i = ⅀ (p i) (λ a → C (transp (λ j → El (p (i ∨ j))) i a))

  -- Push a `subst (FreeOps K) p` past the *first* argument of an outer `graft`.
  -- The result lives in `FreeOps K (⅀ A' C)` on both sides; we move the subst
  -- onto a `⅀-subst-path`-shaped reindexing of the inner `graft`. Proved by
  -- exhibiting a direct cubical filler — at each `i`, `graft` is applied to the
  -- partial-transport of `t` (so the first `FreeOps` argument lives in
  -- `FreeOps K (p i)`) and the per-fibre function `f` is reparameterised along
  -- the corresponding partial `El`-transport. `fromPathP` of the filler is the
  -- desired equation.
  opaque
    graft-subst-fst : (K : Code → Type ℓk) {A A' : Code} (p : A ≡ A')
                      (C : El A' → Code) (t : FreeOps K A)
                      (f : (a : El A') → FreeOps K (C a))
                    → graft K A' C (subst (FreeOps K) p t) f
                    ≡ subst (FreeOps K) (⅀-subst-path p C)
                            (graft K A (λ a → C (transport (cong El p) a)) t
                                   (λ a → f (transport (cong El p) a)))
    graft-subst-fst K {A} {A'} p C t f = sym (fromPathP filler)
      where
        filler : PathP (λ i → FreeOps K (⅀-subst-path p C i))
                       (graft K A (λ a → C (transport (cong El p) a)) t
                              (λ a → f (transport (cong El p) a)))
                       (graft K A' C (subst (FreeOps K) p t) f)
        filler i = graft K (p i) (λ a → C (transp (λ j → El (p (i ∨ j))) i a))
                         (transp (λ k → FreeOps K (p (i ∧ k))) (~ i) t)
                         (λ a → f (transp (λ j → El (p (i ∨ j))) i a))

  -- Push `subst (FreeOps K) (cong (⅀ A) q)` past the *second* (per-fibre)
  -- argument of an outer `graft`. The codomain family rebases from `C` to `C'`
  -- along `q`, and each per-fibre subtree `f a` is independently substed along
  -- the corresponding `funExt⁻ q a`. Proved by the dual filler to
  -- `graft-subst-fst`: at each `i`, `graft` runs with the same tree `t` but the
  -- codomain at `q i` and a partial `q`-transport on each `f a`.
  opaque
    graft-subst-snd : (K : Code → Type ℓk) (A : Code) {C C' : El A → Code}
                      (q : C ≡ C') (t : FreeOps K A)
                      (f : (a : El A) → FreeOps K (C a))
                    → subst (FreeOps K) (cong (⅀ A) q) (graft K A C t f)
                    ≡ graft K A C' t (λ a → subst (FreeOps K) (funExt⁻ q a) (f a))
    graft-subst-snd K A {C} {C'} q t f = fromPathP filler
      where
        filler : PathP (λ i → FreeOps K (⅀ A (q i)))
                       (graft K A C t f)
                       (graft K A C' t (λ a → subst (FreeOps K) (funExt⁻ q a) (f a)))
        filler i = graft K A (q i) t (λ a → transp (λ k → FreeOps K (q (i ∧ k) a)) (~ i) (f a))

  -- Transport along `⅀IdlD 𝒰 D` (the path `D α ≡ ⅀ 𝜏 D` with `α = invEq ⟦𝜏⟧ tt`)
  -- coincides with the canonical inverse-Σ pre-image `invEq (⟦⅀⟧ 𝜏 D) (α , b)`.
  -- This is the leaf-case analog of `transp-⅀AssocD-pair` (§5): a once-and-for-all
  -- characterisation of how the `⅀IdlD` path acts on a canonical input.
  -- Proof: split `⅀IdlD = sym (⅀Idl 𝒰 (D α)) ∙ cong (⅀ 𝜏) const-X-D` via
  -- `congFunct` + `substComposite`, then apply `⟦⅀Idl⟧` (relating `ua (⅀Idl≃)` to
  -- `cong El (Inj …)`) on the first factor and `⟦⅀⟧-natural-snd` on the second.
  -- The per-fibre transport at the `α`-fibre reduces to the identity because
  -- `El 𝜏` is a proposition, so `retEq ⟦𝜏⟧ α ≡ refl`.
  opaque
   transp-⅀IdlD : (D : El 𝜏 → Code) (b : El (D (invEq ⟦𝜏⟧ tt)))
               → transport (cong El (⅀IdlD 𝒰 D)) b ≡ invEq (⟦⅀⟧ 𝜏 D) (invEq ⟦𝜏⟧ tt , b)
   transp-⅀IdlD D b =
      transport (cong El (sym (⅀Idl 𝒰 (D α)) ∙ cong (⅀ 𝜏) const-X-D)) b
    ≡⟨ cong (λ p → transport p b) (congFunct El (sym (⅀Idl 𝒰 (D α))) (cong (⅀ 𝜏) const-X-D)) ⟩
      transport (cong El (sym (⅀Idl 𝒰 (D α))) ∙ cong El (cong (⅀ 𝜏) const-X-D)) b
    ≡⟨ substComposite (λ X → X)
                      (cong El (sym (⅀Idl 𝒰 (D α))))
                      (cong El (cong (⅀ 𝜏) const-X-D)) b ⟩
      transport (cong El (cong (⅀ 𝜏) const-X-D))
                (transport (cong El (sym (⅀Idl 𝒰 (D α)))) b)
    ≡⟨ cong (transport (cong El (cong (⅀ 𝜏) const-X-D))) half-1 ⟩
      transport (cong El (cong (⅀ 𝜏) const-X-D))
                (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
    ≡⟨ half-2 ⟩
      invEq (⟦⅀⟧ 𝜏 D) (α , b)
    ∎
    where
      α : El 𝜏
      α = invEq ⟦𝜏⟧ tt

      const-X-D : (λ (_ : El 𝜏) → D α) ≡ D
      const-X-D = funExt (λ e → cong D (retEq ⟦𝜏⟧ e))

      -- First factor: transport along `sym (⅀Idl 𝒰 (D α))` is `invEq (⅀Idl≃ (D α))`
      -- (via `⟦⅀Idl⟧` + `uaInvEquiv` + `uaβ`), which by `invEq-⅀Idl` agrees with
      -- the canonical `invEq (⟦⅀⟧ 𝜏 (const (D α))) (α , _)` form.
      half-1 : transport (cong El (sym (⅀Idl 𝒰 (D α)))) b
             ≡ invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)
      half-1 =
          transport (sym (cong El (⅀Idl 𝒰 (D α)))) b
        ≡⟨ cong (λ p → transport (sym p) b) (sym (⟦⅀Idl⟧ (D α))) ⟩
          transport (sym (ua (⅀Idl≃ (D α)))) b
        ≡⟨ cong (λ p → transport p b) (sym (uaInvEquiv (⅀Idl≃ (D α)))) ⟩
          transport (ua (invEquiv (⅀Idl≃ (D α)))) b
        ≡⟨ uaβ (invEquiv (⅀Idl≃ (D α))) b ⟩
          invEq (⅀Idl≃ (D α)) b
        ≡⟨ sym (invEq-⅀Idl (D α) b) ⟩
          invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)
        ∎

      -- Second factor: transport along `cong (⅀ 𝜏) const-X-D` factors via
      -- `⟦⅀⟧-natural-snd`. At the `α`-fibre, the per-fibre transport reduces to
      -- the identity because `El 𝜏` is a proposition — hence `retEq ⟦𝜏⟧ α ≡ refl`,
      -- which makes `funExt⁻ const-X-D α ≡ refl` and the corresponding
      -- `pathToEquiv (cong El _) ≡ idEquiv`.
      retEq-𝜏-refl : retEq ⟦𝜏⟧ α ≡ refl
      retEq-𝜏-refl = isProp→isSet (isPropEl𝜏 𝒰) α α (retEq ⟦𝜏⟧ α) refl

      σ-snd-α-id : pathToEquiv (cong El (funExt⁻ const-X-D α)) ≡ idEquiv (El (D α))
      σ-snd-α-id = cong pathToEquiv (cong (cong El) (cong (cong D) retEq-𝜏-refl))
                 ∙ pathToEquivRefl

      half-2 : transport (cong El (cong (⅀ 𝜏) const-X-D))
                         (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
             ≡ invEq (⟦⅀⟧ 𝜏 D) (α , b)
      half-2 =
          transport (cong (λ B' → El (⅀ 𝜏 B')) const-X-D)
                    (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
        ≡⟨ cong (λ e → equivFun e (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)))
                (⟦⅀⟧-natural-snd 𝒰 𝜏 const-X-D) ⟩
          equivFun (compEquiv (⟦⅀⟧ 𝜏 (λ _ → D α))
                              (compEquiv (Σ-cong-equiv-snd {A = El 𝜏}
                                            {B = λ _ → El (D α)} {B' = λ a → El (D a)}
                                            (λ a → pathToEquiv (cong El (funExt⁻ const-X-D a))))
                                         (invEquiv (⟦⅀⟧ 𝜏 D))))
                   (invEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b))
        ≡⟨ cong (equivFun (compEquiv (Σ-cong-equiv-snd {A = El 𝜏}
                                         {B = λ _ → El (D α)} {B' = λ a → El (D a)}
                                         (λ a → pathToEquiv (cong El (funExt⁻ const-X-D a))))
                                      (invEquiv (⟦⅀⟧ 𝜏 D))))
                (secEq (⟦⅀⟧ 𝜏 (λ _ → D α)) (α , b)) ⟩
          equivFun (invEquiv (⟦⅀⟧ 𝜏 D))
                   (equivFun (Σ-cong-equiv-snd {A = El 𝜏}
                                {B = λ _ → El (D α)} {B' = λ a → El (D a)}
                                (λ a → pathToEquiv (cong El (funExt⁻ const-X-D a))))
                            (α , b))
        ≡⟨ cong (equivFun (invEquiv (⟦⅀⟧ 𝜏 D)))
                (ΣPathP (refl , cong (λ e → equivFun e b) σ-snd-α-id)) ⟩
          invEq (⟦⅀⟧ 𝜏 D) (α , b)
        ∎

  -- Transport along `⅀-subst-path p C` computes via the canonical Σ-rebase:
  -- given `y : El (⅀ A (C ∘ transport p))`, send `(a , c) = equivFun ⟦⅀⟧ y` under
  -- the `Σ` shuffle to `(transport p a , c)` and back via `invEq ⟦⅀⟧` at the
  -- target. Used in `graft-assoc`'s `eq-leaf` chain alongside `⅀AssocD` reductions.
  --
  -- Proof: `J` on `p`. At `p = refl`, `⅀-subst-path refl C` reduces definitionally
  -- to `cong (⅀ A) B-path` where `B-path` varies the second arg via a `transp`
  -- on a constant family; the equation then follows from `⟦⅀⟧-natural-snd`
  -- plus a `ΣPathP` that swaps the per-fibre transport (Σ-snd form) for the
  -- first-component `transport-refl` form (Σ-fst form).
  transp-⅀-subst-path : {A A' : Code} (p : A ≡ A') (C : El A' → Code)
                        (y : El (⅀ A (λ a → C (transport (cong El p) a))))
                      → transport (cong El (⅀-subst-path p C)) y
                      ≡ invEq (⟦⅀⟧ A' C)
                              (transport (cong El p)
                                         (fst (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y)) ,
                               snd (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y))
  transp-⅀-subst-path {A} {A'} = J motive at-refl
    where
      motive : (A' : Code) → A ≡ A' → Type _
      motive A' p = (C : El A' → Code)
                    (y : El (⅀ A (λ a → C (transport (cong El p) a))))
                  → transport (cong El (⅀-subst-path p C)) y
                  ≡ invEq (⟦⅀⟧ A' C)
                          (transport (cong El p)
                                     (fst (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y)) ,
                           snd (equivFun (⟦⅀⟧ A (λ a → C (transport (cong El p) a))) y))

      at-refl : motive A refl
      at-refl C y =
          transport (cong (λ B → El (⅀ A B)) B-path) y
        ≡⟨ cong (λ e → equivFun e y) (⟦⅀⟧-natural-snd 𝒰 A B-path) ⟩
          invEq (⟦⅀⟧ A C) (a , transport (cong El (funExt⁻ B-path a)) c)
        ≡⟨ cong (invEq (⟦⅀⟧ A C)) pair-eq ⟩
          invEq (⟦⅀⟧ A C) (transport refl a , c)
        ∎
        where
          B-path : (λ (a' : El A) → C (transport refl a')) ≡ C
          B-path i a' = C (transp (λ _ → El A) i a')

          ⟦⅀⟧-of-y : Σ (El A) (λ a' → El (C (transport refl a')))
          ⟦⅀⟧-of-y = equivFun (⟦⅀⟧ A (λ a' → C (transport refl a'))) y

          a : El A
          a = fst ⟦⅀⟧-of-y

          c : El (C (transport refl a))
          c = snd ⟦⅀⟧-of-y

          pair-eq : (a , transport (cong El (funExt⁻ B-path a)) c) ≡ (transport refl a , c)
          pair-eq = ΣPathP ( sym (transportRefl a)
                          , λ i → transport-filler (cong El (funExt⁻ B-path a)) c (~ i))

  -- Equivalence-form of `transp-⅀-subst-path`: `pathToEquiv (cong El (⅀-subst-path p C))`
  -- factors as `⟦⅀⟧ ⨟ Σ-cong-equiv-fst (pathToEquiv (cong El p)) ⨟ invEquiv ⟦⅀⟧`.
  -- One-line consequence of `transp-⅀-subst-path` via `equivEq + funExt`, since
  -- `equivFun (pathToEquiv P) ≡ transport P` and `equivFun (Σ-cong-equiv-fst e) (a, b)
  -- ≡ (equivFun e a, b)` definitionally.
  opaque
    ⅀-subst-path-equiv :
      {A A' : Code} (p : A ≡ A') (C : El A' → Code)
      → pathToEquiv (cong El (⅀-subst-path p C))
      ≡ compEquiv (⟦⅀⟧ A (λ a → C (transport (cong El p) a)))
                  (compEquiv (Σ-cong-equiv-fst {B = λ a → El (C a)}
                                (pathToEquiv (cong El p)))
                             (invEquiv (⟦⅀⟧ A' C)))
    ⅀-subst-path-equiv p C = equivEq (funExt (transp-⅀-subst-path p C))

  -- `⅀Assoc-C' A B C` unfolds definitionally to its `η`-form on Σ,
  -- i.e. `λ ab → C (fst (⟦⅀⟧ ab)) (snd (⟦⅀⟧ ab))`. We record this with `refl` so
  -- downstream `cong`s can rewrite under it without needing to unfold `⅀Assoc-C'`
  -- by hand. Used by `eq-leaf`'s `funExt-q-decomp`.
  private
    Assoc-C'-uncurry-refl : (A : Code) (B : El A → Code) (C : (a : El A) → El (B a) → Code)
                          → ⅀Assoc-C' A B C
                          ≡ (λ ab → C (fst (equivFun (⟦⅀⟧ A B) ab))
                                       (snd (equivFun (⟦⅀⟧ A B) ab)))
    Assoc-C'-uncurry-refl _ _ _ = refl

  -- ============================================================================
  -- §5  Reduction toolkit
  --
  -- The associativity proof (`graft-assoc`) and to a lesser extent `graft-idr`
  -- repeatedly need to compute *transports along the universe paths*
  -- `Inj (⅀Assoc≃ A B C)` and `⅀AssocD 𝒰 A B C` applied to a *canonical
  -- pair* `invEq (⟦⅀⟧ A …) (a , z)`. Every such site follows the same
  -- five-step recipe; the toolkit below extracts it once. Each subsequent
  -- call site shrinks from ~30 lines of substComposite/cong bookkeeping to
  -- a 1-line specialisation.
  --
  -- Recipe:
  --   (a) `Assoc-cont A B C p` — the explicit Σ-shuffle that
  --       `equivFun (⅀Assoc≃ A B C)` unfolds to (this is `compEquiv`
  --       reducing definitionally on Σ).
  --   (b) `Assoc-cont-at-pair` — `equivFun (⅀Assoc≃ A B C) (invEq ⟦⅀⟧ p) ≡
  --       Assoc-cont A B C p`, by `cong (Assoc-cont _) (secEq …)`.
  --   (c) `step-Assoc-on-pair` — `transport (cong El (Inj (⅀Assoc≃ A B C))) ∘
  --       invEq ⟦⅀⟧ ≡ Assoc-cont A B C`, via `⟦⅀Assoc⟧ + uaβ`.
  --   (d) `transp-⅀AssocD-pair` — the analogous fact for the whole
  --       `⅀AssocD 𝒰 A B C` path (which is `Inj (⅀Assoc≃) ∙ cong (⅀ _) C'-eq`),
  --       built by composing (c) with a `⟦⅀⟧-natural-snd` step.
  --   (e) `adj-coh` — adjunction coherence for an arbitrary equivalence,
  --       used inside (d) to relate the `funExt⁻ C'-eq` transport to a
  --       `secEq`-driven one (this is what `c-of-eq` in the original
  --       node case did at three different abstraction levels).
  -- ============================================================================

  -- (e) Adjunction coherence: `invEq` of `secEq` equals `retEq` of `invEq`.
  --     A general groupoid fact derived from `EquivJ` at `idEquiv`.
  adj-coh : ∀ {ℓ} {X Y : Type ℓ} (e : X ≃ Y) (y : Y)
          → cong (invEq e) (secEq e y) ≡ retEq e (invEq e y)
  adj-coh {Y = Y} e =
    EquivJ (λ _ e' → (y : Y) → cong (invEq e') (secEq e' y) ≡ retEq e' (invEq e' y))
           (λ _ → refl) e

  -- (a) The explicit Σ-shuffle behind `equivFun (⅀Assoc≃ A B C)`.
  --     `⅀Assoc≃ A B C` is defined in Universe/Base as a five-fold `compEquiv`,
  --     so `equivFun (⅀Assoc≃ A B C) y` reduces definitionally to
  --     `Assoc-cont A B C (equivFun (⟦⅀⟧ A _) y)`. Naming the shuffle once
  --     means downstream sites never have to inline the Σ bookkeeping.
  Assoc-cont : (A : Code) (B : El A → Code)
               (C : (a : El A) → El (B a) → Code)
               (p : Σ (El A) (λ a → El (⅀ (B a) (C a))))
             → El (⅀ (⅀ A B) (⅀Assoc-C' A B C))
  Assoc-cont A B C p =
    invEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C))
          (invEq (Σ-cong-equiv-fst {B = λ ab → El (C (fst ab) (snd ab))} (⟦⅀⟧ A B))
                 (invEq Σ-assoc-≃
                        (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B a) (C a))) p)))

  opaque
    -- (b) Apply `⅀Assoc≃` to a canonical pair `invEq ⟦⅀⟧ p`. The only
    --     propositional step is `secEq`; the rest is definitional.
    Assoc-cont-at-pair
      : (A : Code) (B : El A → Code) (C : (a : El A) → El (B a) → Code)
        (p : Σ (El A) (λ a → El (⅀ (B a) (C a))))
      → equivFun (⅀Assoc≃ A B C)
                 (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)
      ≡ Assoc-cont A B C p
    Assoc-cont-at-pair A B C p =
      cong (Assoc-cont A B C) (secEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)

  opaque
    -- (c) Push `transport (cong El (Inj (⅀Assoc≃ …)))` through a canonical
    --     pair input. Combines `⟦⅀Assoc⟧` (`Inj`-image of `⅀Assoc≃` equals
    --     `ua` of `⅀Assoc≃`) with `uaβ` and `Assoc-cont-at-pair`.
    step-Assoc-on-pair
      : (A : Code) (B : El A → Code) (C : (a : El A) → El (B a) → Code)
        (p : Σ (El A) (λ a → El (⅀ (B a) (C a))))
      → transport (cong El (Inj (⅀Assoc≃ A B C)))
                  (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)
      ≡ Assoc-cont A B C p
    step-Assoc-on-pair A B C p =
        cong (λ q → transport q (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p))
             (sym (⟦⅀Assoc⟧ A B C))
      ∙ uaβ (⅀Assoc≃ A B C) (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a))) p)
      ∙ Assoc-cont-at-pair A B C p

  opaque
    -- (d) Push `transport (cong El (⅀AssocD 𝒰 A B C))` through a canonical
    --     pair input. `⅀AssocD A B C` is `Inj (⅀Assoc≃ A B C') ∙ cong (⅀ (⅀ A B)) C'-eq`
    --     where `C' a b = C (invEq (⟦⅀⟧ A B) (a , b))` and
    --     `C'-eq : ⅀Assoc-C' A B C' ≡ C` is the `retEq`-driven funExt.
    --     Two sites in `graft-assoc`'s node case
    --     (`transp-⅀AssocD-LHS-on-pair`, `transp-⅀AssocD-RHS-on-pair` in
    --     pre-refactor terminology) collapse to one-liner specialisations.
    transp-⅀AssocD-pair
      : (A : Code) (B : El A → Code) (C : El (⅀ A B) → Code)
        (a : El A)
        (z : El (⅀ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))))
      → transport (cong El (⅀AssocD 𝒰 A B C))
                  (invEq (⟦⅀⟧ A (λ a' → ⅀ (B a') (λ b → C (invEq (⟦⅀⟧ A B) (a' , b)))))
                         (a , z))
      ≡ invEq (⟦⅀⟧ (⅀ A B) C)
              ( invEq (⟦⅀⟧ A B) (a , fst (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z))
              , snd (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z))
    transp-⅀AssocD-pair A B C a z =
        cong (λ q → transport q input)
             (congFunct El (Inj (⅀Assoc≃ A B C')) (cong (⅀ (⅀ A B)) C'-eq))
      ∙ substComposite (λ X → X)
                       (cong El (Inj (⅀Assoc≃ A B C')))
                       (cong El (cong (⅀ (⅀ A B)) C'-eq))
                       input
      ∙ cong transp-C'-eq (step-Assoc-on-pair A B C' (a , z))
      ∙ transp-C'-eq-canonical
      ∙ cong (λ w → invEq (⟦⅀⟧ (⅀ A B) C) (paired-ab , w))
             (sym c-restore)
      where
        -- The inner family used by `⅀AssocD`: rebases `C` from `El (⅀ A B)`
        -- to `(a : El A) → El (B a)` via the canonical `invEq` pre-image.
        C' : (a : El A) → El (B a) → Code
        C' a' b = C (invEq (⟦⅀⟧ A B) (a' , b))

        -- The codomain-correction path used by `⅀AssocD`: at every `x : El (⅀ A B)`
        -- the post-shuffle codomain `⅀Assoc-C' A B C'` evaluates by `retEq` to `C`.
        C'-eq : ⅀Assoc-C' A B C' ≡ C
        C'-eq = funExt (λ x → cong C (retEq (⟦⅀⟧ A B) x))

        -- The transport along `cong (⅀ (⅀ A B)) C'-eq` (the second leg of
        -- `⅀AssocD`). Named so the proof body reads as a single chain of `cong`s.
        transp-C'-eq : El (⅀ (⅀ A B) (⅀Assoc-C' A B C')) → El (⅀ (⅀ A B) C)
        transp-C'-eq = transport (cong (λ B'' → El (⅀ (⅀ A B) B'')) C'-eq)

        input : El (⅀ A (λ a' → ⅀ (B a') (λ b → C (invEq (⟦⅀⟧ A B) (a' , b)))))
        input = invEq (⟦⅀⟧ A (λ a' → ⅀ (B a') (λ b → C (invEq (⟦⅀⟧ A B) (a' , b))))) (a , z)

        b-of : El (B a)
        b-of = fst (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z)

        w-of : El (C (invEq (⟦⅀⟧ A B) (a , b-of)))
        w-of = snd (equivFun (⟦⅀⟧ (B a) (λ b → C (invEq (⟦⅀⟧ A B) (a , b)))) z)

        paired-ab : El (⅀ A B)
        paired-ab = invEq (⟦⅀⟧ A B) (a , b-of)

        -- The `subst`-shifted second component arising inside `Assoc-cont A B C' (a , z)`
        -- after the inverse-of-Σ-cong-equiv-fst step.
        substed-w : El (⅀Assoc-C' A B C' paired-ab)
        substed-w = subst (λ ab → El (C' (fst ab) (snd ab)))
                          (sym (secEq (⟦⅀⟧ A B) (a , b-of))) w-of

        -- Step (e), local form: transport along the `funExt⁻ C'-eq`-image of
        -- `paired-ab` recovers `w-of` from `substed-w`. The composed path
        --   cong (λ ab → El (C' …)) (sym (secEq ⟦⅀⟧ (a , b-of)))
        --   ∙ cong El (funExt⁻ C'-eq paired-ab)
        -- collapses to `refl` by `adj-coh` (its two factors are exact inverses
        -- of one another modulo `cong (cong _) …`).
        opaque
          c-restore : w-of ≡ transport (cong El (funExt⁻ C'-eq paired-ab)) substed-w
          c-restore =
              sym (transportRefl w-of)
            ∙ cong (λ q → transport q w-of)
                   (sym (lCancel (cong (λ ab → El (C' (fst ab) (snd ab)))
                                        (secEq (⟦⅀⟧ A B) (a , b-of)))))
            ∙ cong (λ q → transport (cong (λ ab → El (C' (fst ab) (snd ab)))
                                            (sym (secEq (⟦⅀⟧ A B) (a , b-of))) ∙ q)
                                     w-of)
                   (sym key-eq-local)
            ∙ substComposite (λ X → X)
                             (cong (λ ab → El (C' (fst ab) (snd ab)))
                                   (sym (secEq (⟦⅀⟧ A B) (a , b-of))))
                             (cong El (funExt⁻ C'-eq paired-ab))
                             w-of
            where
              -- `funExt⁻ C'-eq paired-ab = cong C (retEq ⟦⅀⟧ paired-ab)`
              -- which by `adj-coh` agrees with `cong (λ ab → C' (fst ab) (snd ab))`
              -- of `secEq ⟦⅀⟧ (a , b-of)`.
              key-eq-local : cong El (funExt⁻ C'-eq paired-ab)
                           ≡ cong (λ ab → El (C' (fst ab) (snd ab)))
                                  (secEq (⟦⅀⟧ A B) (a , b-of))
              key-eq-local = cong (cong (λ x → El (C x)))
                                  (sym (adj-coh (⟦⅀⟧ A B) (a , b-of)))

        -- Transport-along-`C'-eq` on the explicit `Assoc-cont` form factors via
        -- `⟦⅀⟧-natural-snd` (second-argument naturality of `⟦⅀⟧`) plus a `secEq`
        -- cancellation that lands us back in the canonical Σ-pair shape.
        opaque
          transp-C'-eq-canonical
            : transp-C'-eq (Assoc-cont A B C' (a , z))
            ≡ invEq (⟦⅀⟧ (⅀ A B) C)
                    ( paired-ab
                    , transport (cong El (funExt⁻ C'-eq paired-ab)) substed-w)
          transp-C'-eq-canonical =
              cong (λ e → equivFun e (Assoc-cont A B C' (a , z)))
                   (⟦⅀⟧-natural-snd 𝒰 (⅀ A B) C'-eq)
            ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A B) C)
                                (fst p ,
                                 transport (cong El (funExt⁻ C'-eq (fst p))) (snd p)))
                   (secEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C'))
                          (paired-ab , substed-w))

  -- ============================================================================
  -- §6  Left identity: graft-idl
  --
  -- Grafting at a `leaf` produces the right-hand subtree, modulo the canonical
  -- path `⅀ 𝜏 (λ _ → A) ≡ A`. For the constant codomain `X = λ _ → A`, the
  -- helper `⅀IdlD 𝒰 X` used inside `graft K 𝜏 (λ _ → A) leaf (λ _ → t)`
  -- reduces definitionally to `sym (Inj (⅀Idl≃ A)) ∙ refl`, so composing with
  -- `Inj (⅀Idl≃ A)` cancels. Following FreeOperad.tex §9 line 280 onwards.
  -- ============================================================================
  graft-idl : (K : Code → Type ℓk) (A : Code) (t : FreeOps K A)
            → PathP (λ i → FreeOps K (Inj (⅀Idl≃ A) i))
                    (graft K 𝜏 (λ _ → A) leaf (λ _ → t)) t
  graft-idl K A t = toPathP eq
    where
      opaque
        reduce : ⅀IdlD 𝒰 (λ _ → A) ∙ Inj (⅀Idl≃ A) ≡ refl
        reduce =
          cong (_∙ Inj (⅀Idl≃ A)) (sym (rUnit (sym (Inj (⅀Idl≃ A)))))
          ∙ lCancel (Inj (⅀Idl≃ A))

        eq : transport (λ i → FreeOps K (Inj (⅀Idl≃ A) i))
                       (graft K 𝜏 (λ _ → A) leaf (λ _ → t)) ≡ t
        eq = sym (substComposite (FreeOps K) (⅀IdlD 𝒰 (λ _ → A)) (Inj (⅀Idl≃ A)) t)
           ∙ cong (λ p → subst (FreeOps K) p t) reduce
           ∙ substRefl {B = FreeOps K} t

  -- ============================================================================
  -- §7  Right identity: graft-idr
  --
  -- Grafting with leaves at every input is the identity, modulo the canonical
  -- path `⅀ A (λ _ → 𝜏) ≡ A`. Three cases:
  --   * Leaf  (A = 𝜏): both `⅀Idl≃ 𝜏` and `⅀Idr≃ 𝜏` are equivalences between
  --     propositional types, hence propositionally equal; the loop reduces.
  --   * Node  (A = ⅀ A' B'): combine the per-fibre IH via `cong (⅀ A')` of a
  --     funExt path, then transfer across `Code` via an `InjSec`-driven bridge.
  --   * Set:   fill via `isProp→SquareP` (the goal is a prop).
  -- ============================================================================
  graft-idr : (K : Code → Type ℓk) (A : Code) (t : FreeOps K A)
            → PathP (λ i → FreeOps K (Inj (⅀Idr≃ A) i))
                    (graft K A (λ _ → 𝜏) t (λ _ → leaf)) t
  graft-idr K _ leaf = toPathP eq
    where
      opaque
        -- `⅀Idl≃ 𝜏` and `⅀Idr≃ 𝜏` are equivalences between the propositional
        -- types `El (⅀ 𝜏 (λ _ → 𝜏))` and `El 𝜏`, hence propositionally equal.
        idl≡idr : ⅀Idl≃ 𝜏 ≡ ⅀Idr≃ 𝜏
        idl≡idr = propEquivEq (isPropEl-⅀𝜏𝜏 𝒰) (isPropEl𝜏 𝒰) (⅀Idl≃ 𝜏) (⅀Idr≃ 𝜏)

        -- The composite `sym (Inj ⅀Idl≃) ∙ Inj ⅀Idr≃` is the `Inj`-image of a loop
        -- between two equal equivalences, hence is `refl` after rewriting along
        -- `idl≡idr` and applying `lCancel`.
        loop-cancels : sym (Inj (⅀Idl≃ 𝜏)) ∙ Inj (⅀Idr≃ 𝜏) ≡ refl
        loop-cancels = cong (λ e → sym (Inj (⅀Idl≃ 𝜏)) ∙ Inj e) (sym idl≡idr)
                     ∙ lCancel (Inj (⅀Idl≃ 𝜏))

        -- `⅀IdlD 𝒰 (λ _ → 𝜏)` unfolds to `sym (Inj (⅀Idl≃ 𝜏)) ∙ refl`, so the
        -- composite with `Inj (⅀Idr≃ 𝜏)` collapses to the loop above.
        reduce : ⅀IdlD 𝒰 (λ _ → 𝜏) ∙ Inj (⅀Idr≃ 𝜏) ≡ refl
        reduce = cong (_∙ Inj (⅀Idr≃ 𝜏)) (sym (rUnit (sym (Inj (⅀Idl≃ 𝜏)))))
               ∙ loop-cancels

        -- Transport along `Inj (⅀Idr≃ 𝜏)` of the substed leaf equals `leaf` once
        -- the composite path reduces (via `substComposite` + `reduce` + `substRefl`).
        eq : transport (λ i → FreeOps K (Inj (⅀Idr≃ 𝜏) i))
                       (graft K 𝜏 (λ _ → 𝜏) leaf (λ _ → leaf)) ≡ leaf
        eq = sym (substComposite (FreeOps K) (⅀IdlD 𝒰 (λ _ → 𝜏)) (Inj (⅀Idr≃ 𝜏)) leaf)
           ∙ cong (λ p → subst (FreeOps K) p leaf) reduce
           ∙ substRefl {B = FreeOps K} leaf
  graft-idr K _ (node A B k ts) = toPathP eq
    where
      -- Per-fibre Code-level path: `⅀ (B a) (λ _ → 𝜏) ≡ B a`, exhibited as the
      -- `Inj`-image of the per-fibre identity equivalence `⅀Idr≃ (B a)`.
      p : (a : El A) → ⅀ (B a) (λ _ → 𝜏) ≡ B a
      p a = Inj (⅀Idr≃ (B a))

      -- The intermediate node value: the LHS of `graft-idr` after one `graft`
      -- step has unfolded `(node A B k ts)` and substed along `⅀AssocD A B (const 𝜏)`,
      -- before the outer `Inj (⅀Idr≃ (⅀ A B))`-transport closes the gap.
      inner-node : FreeOps K (⅀ A (λ a → ⅀ (B a) (λ _ → 𝜏)))
      inner-node = node A (λ a → ⅀ (B a) (λ _ → 𝜏)) k
                        (λ a → graft K (B a) (λ _ → 𝜏) (ts a) (λ _ → leaf))

      -- Structural heterogeneous path from `inner-node` to `node A B k ts`,
      -- varying the per-fibre codomain along `p` and the per-fibre subtree along
      -- the IH `graft-idr K (B a) (ts a)`.
      node-path : PathP (λ i → FreeOps K (⅀ A (λ a → p a i)))
                        inner-node (node A B k ts)
      node-path i = node A (λ a → p a i) k (λ a → graft-idr K (B a) (ts a) i)

      opaque
        -- Code-level bridge: the path used by the outer `Inj (⅀Idr≃ (⅀ A B))`
        -- transport agrees with the `cong (⅀ A) (funExt p)` path that drives
        -- `node-path`. Strategy: the standard `InjSec` sandwich
        --     `p = sym (InjSec p) ∙ cong Inj (equivs-agree) ∙ InjSec p'`
        -- reduces the goal to an equality of equivalences, which we then
        -- discharge pointwise.
        bridge : ⅀AssocD 𝒰 A B (λ _ → 𝜏) ∙ Inj (⅀Idr≃ (⅀ A B))
               ≡ cong (⅀ A) (funExt p)
        bridge =
            sym (InjSec 𝒰 (⅀AssocD 𝒰 A B (λ _ → 𝜏) ∙ Inj (⅀Idr≃ (⅀ A B))))
          ∙ cong Inj equivs-agree
          ∙ InjSec 𝒰 (cong (⅀ A) (funExt p))
          where
            -- LHS-of-bridge under `cong El` simplifies to `ua (⅀Assoc≃ ⨟ ⅀Idr≃)`.
            -- Path-composition + `⟦⅀Assoc⟧`/`⟦⅀Idr⟧` (which equate `cong El (Inj e)`
            -- with `ua e`) yields `ua (compEquiv …)` via `uaCompEquiv`.
            cong-El-LHS : cong El (⅀AssocD 𝒰 A B (λ _ → 𝜏) ∙ Inj (⅀Idr≃ (⅀ A B)))
                        ≡ ua (compEquiv (⅀Assoc≃ A B (λ _ _ → 𝜏)) (⅀Idr≃ (⅀ A B)))
            cong-El-LHS =
                congFunct El (⅀AssocD 𝒰 A B (λ _ → 𝜏)) (Inj (⅀Idr≃ (⅀ A B)))
              ∙ cong₂ _∙_
                      -- cong El ⅀AssocD ≡ ua ⅀Assoc≃ ∙ refl
                      (congFunct El (Inj (⅀Assoc≃ A B (λ _ _ → 𝜏))) refl
                       ∙ cong₂ _∙_ (sym (⟦⅀Assoc⟧ A B (λ _ _ → 𝜏))) refl
                       ∙ sym (rUnit _))
                      -- cong El (Inj (⅀Idr≃ ⅀AB)) ≡ ua (⅀Idr≃ ⅀AB)
                      (sym (⟦⅀Idr⟧ (⅀ A B)))
              ∙ sym (uaCompEquiv (⅀Assoc≃ A B (λ _ _ → 𝜏)) (⅀Idr≃ (⅀ A B)))

            -- RHS-of-bridge under `cong El` simplifies via `⟦⅀⟧-natural-snd` to
            -- a `Σ-cong-equiv-snd`-shaped composite. For `p a = Inj (⅀Idr≃ (B a))`
            -- the per-fibre `pathToEquiv (cong El (p a))` collapses to `⅀Idr≃ (B a)`
            -- (by `⟦⅀Idr⟧` + `pathToEquiv-ua`).
            cong-El-RHS-equiv : pathToEquiv (cong El (cong (⅀ A) (funExt p)))
                              ≡ compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (λ _ → 𝜏)))
                                          (compEquiv (Σ-cong-equiv-snd {A = El A}
                                                        {B = λ a → El (⅀ (B a) (λ _ → 𝜏))}
                                                        {B' = λ a → El (B a)}
                                                        (λ a → ⅀Idr≃ (B a)))
                                                     (invEquiv (⟦⅀⟧ A B)))
            cong-El-RHS-equiv =
                ⟦⅀⟧-natural-snd 𝒰 A (funExt p)
              ∙ cong (λ f → compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (λ _ → 𝜏)))
                                      (compEquiv (Σ-cong-equiv-snd {A = El A}
                                                    {B = λ a → El (⅀ (B a) (λ _ → 𝜏))}
                                                    {B' = λ a → El (B a)} f)
                                                 (invEquiv (⟦⅀⟧ A B))))
                     (funExt λ a →
                         cong pathToEquiv (cong (cong El) (funExt⁻-funExt p a))
                       ∙ cong pathToEquiv (sym (⟦⅀Idr⟧ (B a)))
                       ∙ pathToEquiv-ua (⅀Idr≃ (B a)))
              where
                funExt⁻-funExt : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
                                   {f g : (a : A) → B a}
                                   (h : (a : A) → f a ≡ g a) (a : A)
                               → funExt⁻ (funExt h) a ≡ h a
                funExt⁻-funExt _ _ = refl

            -- Bridge the two equivalence forms: `compEquiv ⅀Assoc≃ ⅀Idr≃` agrees
            -- with the `Σ-cong-equiv-snd`-based composite. Both send `x` to
            -- `invEq (⟦⅀⟧ A B) (a , b)` where `(a , σ) = ⟦⅀⟧ x` and `(b , _) = ⟦⅀⟧ σ`;
            -- after `equivEq + funExt`, the only non-definitional step is the
            -- single `secEq` invocation cancelling `equivFun ⟦⅀⟧ ∘ invEq ⟦⅀⟧` inside.
            composite-as-Σ : compEquiv (⅀Assoc≃ A B (λ _ _ → 𝜏)) (⅀Idr≃ (⅀ A B))
                           ≡ compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (λ _ → 𝜏)))
                                       (compEquiv (Σ-cong-equiv-snd {A = El A}
                                                     {B = λ a → El (⅀ (B a) (λ _ → 𝜏))}
                                                     {B' = λ a → El (B a)}
                                                     (λ a → ⅀Idr≃ (B a)))
                                                  (invEquiv (⟦⅀⟧ A B)))
            composite-as-Σ = equivEq (funExt λ _ →
              cong (λ w → equivFun Σ-idr-≃ (equivFun (Σ-cong-equiv-snd (λ _ → ⟦𝜏⟧)) w))
                   (secEq (⟦⅀⟧ (⅀ A B) (λ _ → 𝜏)) _))

            equivs-agree : pathToEquiv (cong El (⅀AssocD 𝒰 A B (λ _ → 𝜏) ∙ Inj (⅀Idr≃ (⅀ A B))))
                         ≡ pathToEquiv (cong El (cong (⅀ A) (funExt p)))
            equivs-agree =
                cong pathToEquiv cong-El-LHS
              ∙ pathToEquiv-ua (compEquiv (⅀Assoc≃ A B (λ _ _ → 𝜏)) (⅀Idr≃ (⅀ A B)))
              ∙ composite-as-Σ
              ∙ sym cong-El-RHS-equiv

        node-path-fp : subst (FreeOps K) (cong (⅀ A) (funExt p)) inner-node
                    ≡ node A B k ts
        node-path-fp = fromPathP node-path

        eq : transport (λ i → FreeOps K (Inj (⅀Idr≃ (⅀ A B)) i))
                       (graft K (⅀ A B) (λ _ → 𝜏) (node A B k ts) (λ _ → leaf))
           ≡ node A B k ts
        eq = sym (substComposite (FreeOps K)
                                  (⅀AssocD 𝒰 A B (λ _ → 𝜏))
                                  (Inj (⅀Idr≃ (⅀ A B)))
                                  inner-node)
           ∙ cong (λ pp → subst (FreeOps K) pp inner-node) bridge
           ∙ node-path-fp
  -- Set case: the goal is a `PathP` into the set `FreeOps K A`, which is a
  -- proposition by `isOfHLevelPathP' 1 (set A)`. The square is filled by
  -- recursively applying `graft-idr K A` to the four faces (`x`, `y`, `p kk`,
  -- `q kk`) of the input `set`-cell, then closing the result with `isProp→SquareP`.
  graft-idr K A (set _ x y p q i j) =
    isProp→SquareP
      {B = λ i' j' → PathP (λ i'' → FreeOps K (Inj (⅀Idr≃ A) i''))
                           (graft K A (λ _ → 𝜏) (set A x y p q i' j') (λ _ → leaf))
                           (set A x y p q i' j')}
      (λ _ _ → isOfHLevelPathP' 1 (set A) _ _)
      (λ _ → graft-idr K A x)
      (λ _ → graft-idr K A y)
      (λ kk → graft-idr K A (p kk))
      (λ kk → graft-idr K A (q kk))
      i j

  -- ============================================================================
  -- §8  Associativity: graft-assoc
  --
  -- The heart of the file. Induction on the first tree `t`. Both `leaf` and
  -- `node` cases reduce (after `toPathP`) to a path between substed `graft`
  -- expressions; in each, a Code-level `bridge` aligns the LHS and RHS index
  -- paths so that a structural `subst`/`graft-subst-fst`/`graft-subst-snd`
  -- chain composes the per-fibre IH into the final equality.
  --
  -- Both cases follow the five-step Recipe outlined in §1 / §5: the toolkit
  -- lemma `transp-⅀AssocD-pair` is applied (specialised) at every site where a
  -- transport along `⅀AssocD A B C` is computed on a canonical Σ-pair input.
  -- ============================================================================
  graft-assoc : (K : Code → Type ℓk) (A : Code) (B : El A → Code)
                (C : (a : El A) → El (B a) → Code)
                (t : FreeOps K A) (ts : (a : El A) → FreeOps K (B a))
                (tss : (a : El A) (b : El (B a)) → FreeOps K (C a b))
              → PathP (λ i → FreeOps K (Inj (⅀Assoc≃ A B C) i))
                      (graft K A (λ a → ⅀ (B a) (C a)) t
                            (λ a → graft K (B a) (C a) (ts a) (tss a)))
                      (graft K (⅀ A B) (⅀Assoc-C' A B C)
                            (graft K A B t ts)
                            (λ ab → tss (fst (equivFun (⟦⅀⟧ A B) ab))
                                        (snd (equivFun (⟦⅀⟧ A B) ab))))
  -- Leaf case (A = 𝜏). After `toPathP`, the goal `LHS ≡ RHS` reduces to a
  -- propositional equality between two heavily substed `graft` expressions:
  --   LHS = `transport (Inj (⅀Assoc≃ 𝜏 B C)) (graft 𝜏 D₀ leaf …)` where each
  --       inner subtree is itself a `graft (B a) (C a) (ts a) (tss a)`.
  --   RHS = `graft (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C) (graft 𝜏 B leaf ts) (tss ∘ ⟦⅀⟧)`,
  --       where the inner LHS-graft of RHS contains `subst (⅀IdlD 𝒰 B) (ts α)`
  --       which does *not* reduce on arbitrary HIT-constructor inputs.
  -- Strategy: build a Code-level `bridge` aligning the two index paths via the
  -- standard `InjSec` sandwich, then chain `substComposite`,
  -- `graft-subst-snd`/`graft-subst-fst`, and a pointwise equality `tss-eq` that
  -- transports the per-fibre subtrees `tss α b` across the bridge.
  graft-assoc K _ B C leaf ts tss = toPathP eq-leaf
    where
      -- The canonical element of `El 𝜏`, used as the index of the single
      -- "leaf-fibre" in `⅀ 𝜏 _`.
      α : El 𝜏
      α = invEq ⟦𝜏⟧ tt

      -- The LHS top-level codomain family: at each `a : El 𝜏`, the post-`graft`
      -- index is `⅀ (B a) (C a)`. Only `a = α` matters (since `El 𝜏` is a prop).
      D₀ : El 𝜏 → Code
      D₀ a = ⅀ (B a) (C a)

      -- Transport `El (B α) → El (⅀ 𝜏 B)` along the `⅀IdlD 𝒰 B` path. This is
      -- the operation that `graft K 𝜏 B leaf ts` evaluates `ts α` through.
      transp-B : El (B α) → El (⅀ 𝜏 B)
      transp-B = transport (cong El (⅀IdlD 𝒰 B))

      -- `equivFun ⟦⅀⟧` on a `transp-B b` recovers the canonical pair `(α , b)`:
      -- `transp-⅀IdlD` rewrites `transp-B b` to `invEq ⟦⅀⟧ (α , b)`, then `secEq`
      -- cancels the inner `equivFun ∘ invEq`.
      pair-eq : (b : El (B α)) → equivFun (⟦⅀⟧ 𝜏 B) (transp-B b) ≡ (α , b)
      pair-eq b = cong (equivFun (⟦⅀⟧ 𝜏 B)) (transp-⅀IdlD B b)
                ∙ secEq (⟦⅀⟧ 𝜏 B) (α , b)

      pair-path : (b : El (B α)) → (α , b) ≡ equivFun (⟦⅀⟧ 𝜏 B) (transp-B b)
      pair-path b = sym (pair-eq b)

      -- Uncurried views of `C` and `tss`, used by `cong`/`funExt` rewrites below.
      C-uncurry : Σ (El 𝜏) (λ a → El (B a)) → Code
      C-uncurry (a , b) = C a b

      tss-uncurry : (p : Σ (El 𝜏) (λ a → El (B a))) → FreeOps K (C-uncurry p)
      tss-uncurry (a , b) = tss a b

      -- The RHS-side codomain family on `b : El (B α)`: applying `⅀Assoc-C'` to
      -- the `transp-B b` shape gives `C` evaluated at the canonical pair.
      C' : El (B α) → Code
      C' b = ⅀Assoc-C' 𝜏 B C (transp-B b)

      -- The RHS-side continuation: `tss` re-indexed through `equivFun ⟦⅀⟧ ∘ transp-B`.
      -- Will appear as the inner per-fibre function of the RHS `graft`.
      f' : (b : El (B α)) → FreeOps K (C' b)
      f' b = tss (fst (equivFun (⟦⅀⟧ 𝜏 B) (transp-B b)))
                 (snd (equivFun (⟦⅀⟧ 𝜏 B) (transp-B b)))

      -- Per-fibre Code-level equality `C α b ≡ C' b`, used by `tss-eq` below.
      q-fn : (b : El (B α)) → C α b ≡ C' b
      q-fn b = cong C-uncurry (pair-path b)

      -- The pointwise-bundled version, used inside `graft-subst-snd` calls.
      q : C α ≡ C'
      q = funExt q-fn

      -- Per-fibre: substing `tss α b` along `funExt⁻ q b` gives `f' b`. Proved
      -- by `fromPathP` of `cong tss-uncurry (pair-path b)` — i.e. the heterogeneous
      -- path obtained by `cong`ing `tss-uncurry` along the canonical pair path.
      tss-eq-fn : (b : El (B α)) → subst (FreeOps K) (funExt⁻ q b) (tss α b) ≡ f' b
      tss-eq-fn b = fromPathP {A = λ i → FreeOps K (q-fn b i)}
                              (cong tss-uncurry (pair-path b))

      tss-eq : (λ b → subst (FreeOps K) (funExt⁻ q b) (tss α b)) ≡ f'
      tss-eq = funExt tss-eq-fn

      -- Abbreviation: the `graft` at the leaf-fibre, used as the operand on which
      -- both sides of `eq-leaf` apply substs/transports.
      inner-graft : FreeOps K (⅀ (B α) (C α))
      inner-graft = graft K (B α) (C α) (ts α) (tss α)

      -- The two ends of the `toPathP`-unfolded goal.
      LHS RHS : FreeOps K (Inj (⅀Assoc≃ 𝜏 B C) i1)
      LHS = transport (λ i → FreeOps K (Inj (⅀Assoc≃ 𝜏 B C) i))
                      (graft K 𝜏 (λ a → ⅀ (B a) (C a)) leaf
                             (λ a → graft K (B a) (C a) (ts a) (tss a)))
      RHS = graft K (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)
                  (graft K 𝜏 B leaf ts)
                  (λ ab → tss (fst (equivFun (⟦⅀⟧ 𝜏 B) ab))
                              (snd (equivFun (⟦⅀⟧ 𝜏 B) ab)))

      -- Helpers built below, in the order they are needed by `eq-leaf`:
      --   funExt-q-decomp : decomposes `funExt⁻ q b` along the `pair-path`/
      --                     `⅀Assoc-C'` factorisation.
      --   c₀'-of, snd-PathP, σ-bridge : the Σ-pair bridge that the `bridge` path
      --                     reduces to pointwise (one `secEq` step).
      --   LHS-chain / RHS-chain / pointwise / equivs-agree / bridge : standard
      --                     `InjSec`-sandwich proving the Code-path equality.
      --   eq-leaf : the final 6-step `substComposite`/`graft-subst-{fst,snd}`
      --                     chain that consumes `bridge` and `tss-eq`.

      -- Split `funExt⁻ q b₀` into its two natural factors: the `secEq`-driven
      -- shift on the Σ-pair side and the `transp-⅀IdlD`-driven shift on the
      -- `⅀Assoc-C'` side. The proof is `symDistr` + `congFunct` on the body of
      -- `q-fn`; the final identification of `cong C-uncurry ∘ cong (equivFun ⟦⅀⟧)`
      -- with `cong (⅀Assoc-C' …)` is definitional (`Assoc-C'-uncurry-refl`).
      opaque
        funExt-q-decomp : (b₀ : El (B α))
                        → funExt⁻ q b₀
                        ≡ cong C-uncurry (sym (secEq (⟦⅀⟧ 𝜏 B) (α , b₀)))
                        ∙ cong (⅀Assoc-C' 𝜏 B C) (sym (transp-⅀IdlD B b₀))
        funExt-q-decomp b₀ =
            cong (cong C-uncurry)
                 (symDistr (cong (equivFun (⟦⅀⟧ 𝜏 B)) (transp-⅀IdlD B b₀))
                           (secEq (⟦⅀⟧ 𝜏 B) (α , b₀)))
          ∙ congFunct C-uncurry
                      (sym (secEq (⟦⅀⟧ 𝜏 B) (α , b₀)))
                      (cong (equivFun (⟦⅀⟧ 𝜏 B)) (sym (transp-⅀IdlD B b₀)))

      -- The "shifted" `snd`-component arising on the LHS of `σ-bridge`. Unfolding
      -- `Assoc-cont 𝜏 B C (α , x)` along its inverse-of-`Σ-cong-equiv-fst` step
      -- yields exactly `subst (C ∘ uncurry) (sym (secEq ⟦⅀⟧ (α , b₀))) c₀`, which
      -- is what `c₀'-of x` records. Used as the LHS endpoint of `snd-PathP`.
      c₀'-of : (x : El (⅀ (B α) (C α))) → El (⅀Assoc-C' 𝜏 B C (invEq (⟦⅀⟧ 𝜏 B)
                                                              (α , fst (equivFun (⟦⅀⟧ (B α) (C α)) x))))
      c₀'-of x = subst (λ ab → El (C (fst ab) (snd ab)))
                       (sym (secEq (⟦⅀⟧ 𝜏 B)
                                   (α , fst (equivFun (⟦⅀⟧ (B α) (C α)) x))))
                       (snd (equivFun (⟦⅀⟧ (B α) (C α)) x))

      -- Heterogeneous path bridging the two `snd`-components of `σ-bridge`. Built
      -- as a `transport-filler` (giving the right `i`-line in the ⅀Assoc-C'
      -- direction) glued via `endpoint-fix` to the desired `transport (cong El
      -- (funExt⁻ q b₀))` form. The endpoint adjustment uses `funExt-q-decomp` to
      -- show the two paths agree.
      opaque
        snd-PathP : (x : El (⅀ (B α) (C α)))
                  → PathP (λ i → El (⅀Assoc-C' 𝜏 B C
                                       (sym (transp-⅀IdlD B (fst (equivFun (⟦⅀⟧ (B α) (C α)) x))) i)))
                          (c₀'-of x)
                          (transport (cong El (funExt⁻ q (fst (equivFun (⟦⅀⟧ (B α) (C α)) x))))
                                     (snd (equivFun (⟦⅀⟧ (B α) (C α)) x)))
        snd-PathP x =
          transport-filler
            (cong (λ z → El (⅀Assoc-C' 𝜏 B C z))
                  (sym (transp-⅀IdlD B b₀)))
            (c₀'-of x)
          ▷ endpoint-fix
          where
            b₀ : El (B α)
            b₀ = fst (equivFun (⟦⅀⟧ (B α) (C α)) x)
            c₀ : El (C α b₀)
            c₀ = snd (equivFun (⟦⅀⟧ (B α) (C α)) x)
            endpoint-fix : transport (cong (λ z → El (⅀Assoc-C' 𝜏 B C z))
                                           (sym (transp-⅀IdlD B b₀)))
                                     (c₀'-of x)
                         ≡ transport (cong El (funExt⁻ q b₀)) c₀
            endpoint-fix =
                sym (substComposite (λ X → X)
                                    (cong (λ ab → El (C (fst ab) (snd ab)))
                                          (sym (secEq (⟦⅀⟧ 𝜏 B) (α , b₀))))
                                    (cong (λ z → El (⅀Assoc-C' 𝜏 B C z))
                                          (sym (transp-⅀IdlD B b₀)))
                                    c₀)
              ∙ cong (λ p → transport p c₀)
                     (sym (congFunct El
                            (cong C-uncurry (sym (secEq (⟦⅀⟧ 𝜏 B) (α , b₀))))
                            (cong (⅀Assoc-C' 𝜏 B C) (sym (transp-⅀IdlD B b₀)))))
              ∙ cong (λ p → transport (cong El p) c₀) (sym (funExt-q-decomp b₀))

      -- The Σ-pair bridge inside `invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))`: a path
      -- of pairs whose `fst`-leg is `sym (transp-⅀IdlD B b₀)` and whose `snd`-leg
      -- is `snd-PathP x`. Wrapped in `invEq ⟦⅀⟧` it equates `LHS-chain` and
      -- `RHS-chain`'s endpoints, providing the propositional kernel of `pointwise`.
      opaque
        σ-bridge : (x : El (⅀ (B α) (C α)))
                 → Path (Σ (El (⅀ 𝜏 B)) (λ ab → El (⅀Assoc-C' 𝜏 B C ab)))
                        (invEq (⟦⅀⟧ 𝜏 B) (α , fst (equivFun (⟦⅀⟧ (B α) (C α)) x))
                          , c₀'-of x)
                        (transp-B (fst (equivFun (⟦⅀⟧ (B α) (C α)) x))
                          , transport (cong El (funExt⁻ q (fst (equivFun (⟦⅀⟧ (B α) (C α)) x))))
                                      (snd (equivFun (⟦⅀⟧ (B α) (C α)) x)))
        σ-bridge x = ΣPathP (sym (transp-⅀IdlD B (fst (equivFun (⟦⅀⟧ (B α) (C α)) x)))
                            , snd-PathP x)

      -- The "continuation" of `⅀Assoc≃ 𝜏 B C` after `equivFun (⟦⅀⟧ 𝜏 D₀)` is just
      -- the toolkit's `Assoc-cont 𝜏 B C` (§5). The previous local `⅀Assoc-cont`,
      -- `⅀Assoc-cont-refl`, and `⅀Assoc-cont-at-αx` definitions were renamings of
      -- definitional equalities; with the toolkit they disappear.

      -- Reduces `transport (cong El (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C))) x` to its
      -- canonical Σ-pair form. Strategy:
      --   1. `congFunct` + `substComposite` split the path-composition transport.
      --   2. `transp-⅀IdlD` rewrites the `⅀IdlD`-leg as `invEq ⟦⅀⟧ (α , x)`.
      --   3. The remaining `transport (cong El (Inj (⅀Assoc≃ …)))` on a canonical
      --      `invEq ⟦⅀⟧` pair is the §5 toolkit's `step-Assoc-on-pair`.
      opaque
        LHS-chain : (x : El (⅀ (B α) (C α)))
                  → transport (cong El (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C))) x
                  ≡ invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))
                          (invEq (⟦⅀⟧ 𝜏 B) (α , fst (equivFun (⟦⅀⟧ (B α) (C α)) x))
                          , c₀'-of x)
        LHS-chain x =
            cong (λ p → transport p x)
                 (congFunct El (⅀IdlD 𝒰 D₀) (Inj (⅀Assoc≃ 𝜏 B C)))
          ∙ substComposite (λ X → X)
                           (cong El (⅀IdlD 𝒰 D₀))
                           (cong El (Inj (⅀Assoc≃ 𝜏 B C))) x
          ∙ cong (transport (cong El (Inj (⅀Assoc≃ 𝜏 B C)))) (transp-⅀IdlD D₀ x)
          ∙ step-Assoc-on-pair 𝜏 B C (α , x)

      -- Reduces `transport (cong El (cong (⅀ (B α)) q ∙ ⅀-subst-path …)) x` to its
      -- canonical form. Strategy:
      --   1. `congFunct` + `substComposite` split the path-composition.
      --   2. `⟦⅀⟧-natural-snd` rewrites `transport (cong (⅀ (B α)) q)` as
      --      `invEq ⟦⅀⟧ (b₀-of x , transport (funExt⁻ q) ∘ c₀-of x)` (the
      --      `Σ-cong-equiv-snd` form).
      --   3. `transp-⅀-subst-path` then handles the `⅀-subst-path` leg.
      --   4. A final `secEq (⟦⅀⟧ (B α) C')` cancels the `equivFun ⟦⅀⟧ ∘ invEq ⟦⅀⟧`
      --      that appears inside.
      opaque
        RHS-chain : (x : El (⅀ (B α) (C α)))
                  → transport (cong El (cong (⅀ (B α)) q
                                       ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))) x
                  ≡ invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))
                          (transp-B (fst (equivFun (⟦⅀⟧ (B α) (C α)) x))
                          , transport (cong El (funExt⁻ q (fst (equivFun (⟦⅀⟧ (B α) (C α)) x))))
                                      (snd (equivFun (⟦⅀⟧ (B α) (C α)) x)))
        RHS-chain x =
            cong (λ p → transport p x)
                 (congFunct El (cong (⅀ (B α)) q)
                              (⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C)))
          ∙ substComposite (λ X → X)
                           (cong El (cong (⅀ (B α)) q))
                           (cong El (⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))) x
          ∙ cong (transport (cong El (⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))))
                 transport-q-x
          ∙ transp-⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C)
                                (invEq (⟦⅀⟧ (B α) C') (b₀-of x , c₀-transported x))
          ∙ cong (λ z → invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))
                              (transp-B (fst z) , snd z))
                 (secEq (⟦⅀⟧ (B α) C') (b₀-of x , c₀-transported x))
          where
            b₀-of : (x : El (⅀ (B α) (C α))) → El (B α)
            b₀-of x = fst (equivFun (⟦⅀⟧ (B α) (C α)) x)
            c₀-transported : (x : El (⅀ (B α) (C α))) → El (C' (b₀-of x))
            c₀-transported x = transport (cong El (funExt⁻ q (b₀-of x)))
                                         (snd (equivFun (⟦⅀⟧ (B α) (C α)) x))
            -- Single step in `RHS-chain`: `transport (cong (⅀ (B α)) q)` applied
            -- pointwise is `equivFun (⟦⅀⟧-natural-snd …)` of `x`, which is the
            -- canonical Σ-cong-equiv-snd form.
            transport-q-x : transport (cong El (cong (⅀ (B α)) q)) x
                          ≡ invEq (⟦⅀⟧ (B α) C') (b₀-of x , c₀-transported x)
            transport-q-x =
                cong (λ e → equivFun e x) (⟦⅀⟧-natural-snd 𝒰 (B α) q)

      -- The heart of the bridge proof: at every `x`, `LHS-chain x` and
      -- `RHS-chain x` land in the same `invEq ⟦⅀⟧`-of-Σ-pair shape, and
      -- `σ-bridge x` provides the propositional equality between those Σ-pairs.
      opaque
        pointwise : (x : El (⅀ (B α) (C α)))
                  → transport (cong El (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C))) x
                  ≡ transport (cong El (cong (⅀ (B α)) q
                                        ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))) x
        pointwise x =
            LHS-chain x
          ∙ cong (invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))) (σ-bridge x)
          ∙ sym (RHS-chain x)

      -- Pointwise equality, packaged as `pathToEquiv`-equality.
      equivs-agree : pathToEquiv (cong El (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C)))
                   ≡ pathToEquiv (cong El (cong (⅀ (B α)) q
                                        ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C)))
      equivs-agree = equivEq (funExt pointwise)

      -- Code-level path identity: the LHS index path (`⅀IdlD ∙ Inj (⅀Assoc≃)`)
      -- and the RHS index path (`cong (⅀ (B α)) q ∙ ⅀-subst-path …`) coincide.
      -- Standard `InjSec` sandwich on top of `equivs-agree`.
      opaque
        bridge : ⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C)
               ≡ cong (⅀ (B α)) q ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C)
        bridge =
            sym (InjSec 𝒰 (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C)))
          ∙ cong Inj equivs-agree
          ∙ InjSec 𝒰 (cong (⅀ (B α)) q ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))

      -- The final chain: `bridge` converts LHS's `substComposite` into the RHS's
      -- one, then `graft-subst-snd` + `tss-eq` + `sym graft-subst-fst` push the
      -- substs through the outer `graft` until both sides match.
      eq-leaf : LHS ≡ RHS
      eq-leaf =
          sym (substComposite (FreeOps K) (⅀IdlD 𝒰 D₀)
                              (Inj (⅀Assoc≃ 𝜏 B C)) inner-graft)
        ∙ cong (λ p → subst (FreeOps K) p inner-graft) bridge
        ∙ substComposite (FreeOps K)
                         (cong (⅀ (B α)) q)
                         (⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))
                         inner-graft
        ∙ cong (subst (FreeOps K) (⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C)))
               (graft-subst-snd K (B α) q (ts α) (tss α))
        ∙ cong (λ f → subst (FreeOps K)
                            (⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))
                            (graft K (B α) C' (ts α) f))
               tss-eq
        ∙ sym (graft-subst-fst K (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C) (ts α)
                                  (λ ab → tss (fst (equivFun (⟦⅀⟧ 𝜏 B) ab))
                                              (snd (equivFun (⟦⅀⟧ 𝜏 B) ab))))
  -- Node case (A = ⅀ A' B'). The recursion goes one level deeper than the leaf
  -- case: the per-fibre IH `graft-assoc K (B' a') …` is supplied recursively for
  -- each `a' : El A'`, then lifted by `cong (⅀ A') (funExt per-fibre-Δ)` into a
  -- heterogeneous `node-path-pre-assoc`. A Code-level `bridge-node` aligns the
  -- LHS and RHS index paths; finally a 6-step `substComposite` chain at the
  -- bottom of this `where`-block (`eq-node`) assembles the answer.
  graft-assoc K _ B C (node A' B' k ts') ts tss = toPathP eq-node
    where
      -- The canonical "pairing": `paired a' b' = invEq ⟦⅀⟧ (a' , b')` is the
      -- explicit Σ-pre-image used everywhere `⅀AssocD A' B' _` is unfolded.
      paired : (a' : El A') → El (B' a') → El (⅀ A' B')
      paired a' b' = invEq (⟦⅀⟧ A' B') (a' , b')

      -- Intermediate index family appearing inside `graft K (⅀ A' B') C _ _`'s
      -- node-clause: each `a' : El A'` fibre becomes `⅀ (B' a') (B ∘ paired a')`.
      B'' : El A' → Code
      B'' a' = ⅀ (B' a') (λ b' → B (paired a' b'))

      -- Transport along `⅀AssocD 𝒰 A' B' B`: the universe-path identifying
      -- `⅀ A' B''` with `⅀ (⅀ A' B') B`.
      transp-⅀AB : El (⅀ A' B'') → El (⅀ (⅀ A' B') B)
      transp-⅀AB = transport (cong El (⅀AssocD 𝒰 A' B' B))

      -- The post-`⅀AssocD` codomain on `B''`: rebases `⅀Assoc-C' (⅀ A' B') B C`
      -- through `transp-⅀AB`. The RHS of `graft-assoc` is built over this.
      C1 : El (⅀ A' B'') → Code
      C1 z = ⅀Assoc-C' (⅀ A' B') B C (transp-⅀AB z)

      -- Uncurried views of `C` and `tss` at the top Σ-level (over `⅀ A' B'`).
      -- Provide the `cong`-friendly form used everywhere `Σ`-pair paths arise.
      C-curry-top : Σ (El (⅀ A' B')) (λ ab → El (B ab)) → Code
      C-curry-top (ab , b'') = C ab b''

      tss-curry-top : (p : Σ (El (⅀ A' B')) (λ ab → El (B ab))) → FreeOps K (C-curry-top p)
      tss-curry-top (ab , b'') = tss ab b''

      -- The two endpoints of the `toPathP`-unfolded goal.
      LHS RHS : FreeOps K (Inj (⅀Assoc≃ (⅀ A' B') B C) i1)
      LHS = transport (λ i → FreeOps K (Inj (⅀Assoc≃ (⅀ A' B') B C) i))
                      (graft K (⅀ A' B') (λ a → ⅀ (B a) (C a)) (node A' B' k ts')
                             (λ a → graft K (B a) (C a) (ts a) (tss a)))
      RHS = graft K (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
                  (graft K (⅀ A' B') B (node A' B' k ts') ts)
                  (λ ab → tss (fst (equivFun (⟦⅀⟧ (⅀ A' B') B) ab))
                              (snd (equivFun (⟦⅀⟧ (⅀ A' B') B) ab)))

      -- LHS-side index family: after the inner `graft K (⅀ A' B') C` step of LHS
      -- unfolds on `node A' B' k ts'`, each `a' : El A'` fibre carries the
      -- doubly-Σ-shaped `⅀ (B' a') (⅀ (B ∘ paired a') (C ∘ paired a'))`.
      B-LHS : El A' → Code
      B-LHS a' = ⅀ (B' a') (λ b' → ⅀ (B (paired a' b')) (C (paired a' b')))

      -- The LHS "inner node" before the outer `Inj (⅀Assoc≃ (⅀ A' B') B C)`-transport:
      -- one `node` with codomain family `B-LHS` and per-fibre subtrees
      -- `graft (B' a') _ (ts' a') _`, themselves built from `graft`s on `(ts ∘ paired)`
      -- and `(tss ∘ paired)`.
      inner-LHS-node : FreeOps K (⅀ A' B-LHS)
      inner-LHS-node = node A' B-LHS k
                            (λ a' → graft K (B' a')
                                          (λ b' → ⅀ (B (paired a' b')) (C (paired a' b')))
                                          (ts' a')
                                          (λ b' → graft K (B (paired a' b')) (C (paired a' b'))
                                                        (ts (paired a' b')) (tss (paired a' b'))))

      -- RHS-side index family: after pushing `graft-subst-fst` across the outer
      -- `graft` on the RHS and reducing `graft` at a `node`, each fibre becomes
      -- `⅀ (B'' a') (C1 ∘ invEq ⟦⅀⟧ (a' , _))` — the "post-⅀AssocD" shape.
      B-RHS : El A' → Code
      B-RHS a' = ⅀ (B'' a') (λ b' → C1 (invEq (⟦⅀⟧ A' B'') (a' , b')))

      inner-RHS-node : FreeOps K (⅀ A' B-RHS)
      inner-RHS-node = node A' B-RHS k
                            (λ a' → graft K (B'' a')
                                          (λ b' → C1 (invEq (⟦⅀⟧ A' B'') (a' , b')))
                                          (graft K (B' a') (λ b' → B (paired a' b')) (ts' a')
                                                 (λ b' → ts (paired a' b')))
                                          (λ b' → tss-curry-top
                                                    (equivFun (⟦⅀⟧ (⅀ A' B') B)
                                                              (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , b'))))))

      -- The eq-node proof proceeds in five stages:
      --   (a) Σ-level rebase for transp-⅀AB (transp-⅀AB-factored + ⟦⅀⟧-on-transp).
      --   (b) snd-adjust-a': the codomain functions on B'' a' agree.
      --   (c) Per-fibre IH composed with (b) via graft-subst-snd (per-fibre-Δ-PathP).
      --   (d) node-path-pre-assoc: lift (c) over funExt to obtain
      --       PathP (⅀ A' (λ a' → per-fibre-Δ a' i)) inner-LHS-node inner-RHS-node.
      --   (e) bridge-node + the 6-step substComposite chain to eq-node.

      -- (a) Σ-level rebase for `transp-⅀AB` at canonical Σ-pair inputs `(a' , z)`.
      -- This is the node-case analog of `transp-⅀IdlD`: it characterises the
      -- iterated `equivFun ⟦⅀⟧ ∘ transp-⅀AB ∘ invEq ⟦⅀⟧` combinator and feeds
      -- into both `snd-adjust-a'` and the `bridge-node` chain.

      -- Per-fibre destructuring of `z : El (B'' a')` through `⟦⅀⟧ (B' a') (B ∘ paired a')`.
      -- Bundled in an anonymous parametric module so `b'-of` and `c'-of` are visible
      -- as `(a' : El A') (z : El (B'' a'))`-indexed functions below.
      module _ (a' : El A') (z : El (B'' a')) where
        b'-of : El (B' a')
        b'-of = fst (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) z)
        c'-of : El (B (paired a' b'-of))
        c'-of = snd (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) z)

      -- The "intermediate" family used inside `⅀AssocD 𝒰 A' B' B`'s decomposition:
      -- before applying the `C'-eq` correction, `C-int a b = B (paired a b)`.
      C-int : (a : El A') → El (B' a) → Code
      C-int a b = B (paired a b)

      -- The codomain-correction path that `⅀AssocD A' B' B` builds in: at every
      -- `x : El (⅀ A' B')` the post-shuffle `⅀Assoc-C' A' B' C-int x` evaluates by
      -- `retEq (⟦⅀⟧ A' B') x` to `B x`. This is the `C'-eq` of `transp-⅀AssocD-pair`
      -- specialised to the node case (with γ = B).
      C'-eq : ⅀Assoc-C' A' B' C-int ≡ B
      C'-eq = funExt (λ x → cong B (retEq (⟦⅀⟧ A' B') x))

      -- Steps (a-1) and (a-2) collapse to one call to the §5 toolkit:
      -- `step-Assoc-on-pair A' B' C-int (a' , z)` already returns `Assoc-cont …`.
      -- The previous inner `step-Assoc-on-pair`, `Assoc-cont`, `Assoc-cont-refl`,
      -- `Assoc-cont-explicit` definitions are subsumed; consumers below now go
      -- through the toolkit forms (`Assoc-cont A' B' C-int` and friends).

      -- The transport leg corresponding to the `cong (⅀ (⅀ A' B')) C'-eq` factor
      -- of `⅀AssocD A' B' B`. Named to keep the proof body of `transp-⅀AB-factored`
      -- readable.
      transp-C'-eq : El (⅀ (⅀ A' B') (⅀Assoc-C' A' B' C-int)) → El (⅀ (⅀ A' B') B)
      transp-C'-eq = transport (cong (λ B'' → El (⅀ (⅀ A' B') B'')) C'-eq)

      -- `transp-⅀AB` factors through `transp-C'-eq ∘ Assoc-cont`: split the
      -- `⅀AssocD` path with `congFunct`/`substComposite`, then apply the §5
      -- toolkit's `step-Assoc-on-pair` to the `Inj (⅀Assoc≃ …)`-leg.
      opaque
        transp-⅀AB-factored : (a' : El A') (z : El (B'' a'))
                            → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , z))
                            ≡ transp-C'-eq (Assoc-cont A' B' C-int (a' , z))
        transp-⅀AB-factored a' z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B'') (a' , z)))
                 (congFunct El (Inj (⅀Assoc≃ A' B' C-int)) (cong (⅀ (⅀ A' B')) C'-eq))
          ∙ substComposite (λ X → X)
                           (cong El (Inj (⅀Assoc≃ A' B' C-int)))
                           (cong El (cong (⅀ (⅀ A' B')) C'-eq))
                           (invEq (⟦⅀⟧ A' B'') (a' , z))
          ∙ cong transp-C'-eq (step-Assoc-on-pair A' B' C-int (a' , z))

      -- The "shifted" `c`-component arising when `Assoc-cont A' B' C-int (a' , z)`
      -- unfolds along its inverse-of-`Σ-cong-equiv-fst` step: it `subst`s
      -- `c'-of a' z` along `sym (secEq ⟦⅀⟧ (a' , b'-of a' z))`. The local
      -- specialisation of `substed-w` in §5's `transp-⅀AssocD-pair`.
      substed-c-of : (a' : El A') (z : El (B'' a'))
                   → El (⅀Assoc-C' A' B' C-int (paired a' (b'-of a' z)))
      substed-c-of a' z =
        subst (λ ab → El (C-int (fst ab) (snd ab)))
              (sym (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z)))
              (c'-of a' z)

      -- `transp-C'-eq` applied to a canonical `invEq ⟦⅀⟧` pair lands in another
      -- canonical pair, with the `snd`-component now transported along
      -- `funExt⁻ C'-eq (paired a' (b'-of a' z))`. Proof: `⟦⅀⟧-natural-snd` rewrites
      -- the transport as `equivFun (Σ-cong-equiv-snd …)`, then a `secEq` cancels
      -- the inner `equivFun ⟦⅀⟧ ∘ invEq ⟦⅀⟧`.
      opaque
        transp-C'-eq-on-canonical : (a' : El A') (z : El (B'' a'))
                                  → transp-C'-eq (invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                                                         (paired a' (b'-of a' z) , substed-c-of a' z))
                                  ≡ invEq (⟦⅀⟧ (⅀ A' B') B)
                                          (paired a' (b'-of a' z)
                                          , transport (cong El (funExt⁻ C'-eq (paired a' (b'-of a' z))))
                                                      (substed-c-of a' z))
        transp-C'-eq-on-canonical a' z =
            cong (λ e → equivFun e (invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                                           (paired a' (b'-of a' z) , substed-c-of a' z)))
                 (⟦⅀⟧-natural-snd 𝒰 (⅀ A' B') C'-eq)
          ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') B)
                              (fst p ,
                               transport (cong El (funExt⁻ C'-eq (fst p))) (snd p)))
                 (secEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                        (paired a' (b'-of a' z) , substed-c-of a' z))

      -- Applying `equivFun ⟦⅀⟧` to a canonical `transp-⅀AB (invEq ⟦⅀⟧ (a' , z))`
      -- recovers the Σ-pair `(paired a' (b'-of …) , transport-along-funExt⁻-C'-eq
      -- (substed-c-of …))`. `transp-⅀AB-factored` followed by `transp-C'-eq-on-canonical`
      -- delivers an `invEq ⟦⅀⟧`-of-pair, then `secEq` cancels the outer
      -- `equivFun ∘ invEq` to expose the pair directly.
      opaque
        unfolding transp-⅀AB-factored transp-C'-eq-on-canonical
        ⟦⅀⟧-on-transp : (a' : El A') (z : El (B'' a'))
                      → equivFun (⟦⅀⟧ (⅀ A' B') B)
                                 (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , z)))
                      ≡ (paired a' (b'-of a' z)
                        , transport (cong El (funExt⁻ C'-eq (paired a' (b'-of a' z))))
                                    (substed-c-of a' z))
        ⟦⅀⟧-on-transp a' z =
            cong (equivFun (⟦⅀⟧ (⅀ A' B') B))
                 (transp-⅀AB-factored a' z ∙ transp-C'-eq-on-canonical a' z)
          ∙ secEq (⟦⅀⟧ (⅀ A' B') B) _

      -- `adj-coh` and `key-eq`: `adj-coh` lives at module level (§5 toolkit).
      -- `key-eq` is the C-int-level specialisation `cong El (funExt⁻ C'-eq …) ≡
      -- cong (λ ab → El (C-int (fst ab) (snd ab))) (secEq ⟦⅀⟧ …)`, derived from
      -- `adj-coh` on `⟦⅀⟧ A' B'`.
      opaque
        key-eq : (a' : El A') (z : El (B'' a'))
               → cong El (funExt⁻ C'-eq (paired a' (b'-of a' z)))
               ≡ cong (λ ab → El (C-int (fst ab) (snd ab)))
                      (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z))
        key-eq a' z = cong (cong (λ x → El (B x)))
                           (sym (adj-coh (⟦⅀⟧ A' B') (a' , b'-of a' z)))

      -- Recovers `c'-of a' z` from `substed-c-of a' z` by transporting along
      -- `cong El (funExt⁻ C'-eq (paired a' (b'-of a' z)))`. The two subst paths
      -- (the inner `secEq`-driven shift and the outer `funExt⁻ C'-eq` cong) are
      -- exact inverses modulo `key-eq`; their composite `lCancel`s to `refl`,
      -- and `transportRefl` then identifies the result with `c'-of`.
      opaque
        c'-of-eq : (a' : El A') (z : El (B'' a'))
                 → c'-of a' z
                 ≡ transport (cong El (funExt⁻ C'-eq (paired a' (b'-of a' z))))
                             (substed-c-of a' z)
        c'-of-eq a' z =
            sym (transportRefl (c'-of a' z))
          ∙ cong (λ p → transport p (c'-of a' z))
                 (sym (lCancel (cong (λ ab → El (C-int (fst ab) (snd ab)))
                                      (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z)))))
          ∙ cong (λ p → transport (cong (λ ab → El (C-int (fst ab) (snd ab)))
                                         (sym (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z))) ∙ p)
                                   (c'-of a' z))
                 (sym (key-eq a' z))
          ∙ substComposite (λ X → X)
                           (cong (λ ab → El (C-int (fst ab) (snd ab)))
                                 (sym (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z))))
                           (cong El (funExt⁻ C'-eq (paired a' (b'-of a' z))))
                           (c'-of a' z)

      -- (b) `snd-adjust-a' a'`: the LHS-side and RHS-side codomain families on
      -- `B'' a'` agree. Concretely,
      --   LHS = ⅀Assoc-C' (B' a') (B ∘ paired a') (C ∘ paired a')
      --       = λ z. C (paired a' (fst ⟦⅀⟧z)) (snd ⟦⅀⟧z)
      --   RHS = λ z. C1 (invEq ⟦⅀⟧A'B'' (a' , z))
      --       = λ z. C-curry-top (equivFun ⟦⅀⟧ (transp-⅀AB (invEq ⟦⅀⟧A'B'' (a' , z))))
      -- The funExt bridge factors as two `cong C-curry-top` steps: a `c'-of-eq`-shift
      -- on the `snd`-component, then `sym (⟦⅀⟧-on-transp …)` to swap the LHS pair
      -- form for the RHS `equivFun ⟦⅀⟧ ∘ transp-⅀AB ∘ invEq ⟦⅀⟧` form.
      opaque
        snd-adjust-a' : (a' : El A')
                      → ⅀Assoc-C' (B' a') (λ b' → B (paired a' b')) (λ b' b'' → C (paired a' b') b'')
                      ≡ (λ z → C1 (invEq (⟦⅀⟧ A' B'') (a' , z)))
        snd-adjust-a' a' = funExt (λ z →
            cong C-curry-top (ΣPathP (refl , c'-of-eq a' z))
          ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a' z)))

      -- (c) Per-fibre `PathP`. The per-fibre IH `graft-assoc K (B' a') …`
      -- provides a heterogeneous path over `Inj (⅀Assoc≃ …)`. Its RHS endpoint
      -- has codomain family `⅀Assoc-C' (B' a') …`; one further `subst` along
      -- `cong (⅀ (B'' a')) (snd-adjust-a' a')` (handled by `step2` below) lands
      -- it at the actual RHS codomain `λ z. C1 (invEq ⟦⅀⟧ (a' , z))`.

      -- LHS endpoint of the per-fibre IH at fibre `a'`: the "inner-inner" graft
      -- of LHS, parameterised on `(B (paired a' _), C (paired a' _))`.
      per-fibre-IH-from : (a' : El A') → FreeOps K (B-LHS a')
      per-fibre-IH-from a' =
        graft K (B' a') (λ b' → ⅀ (B (paired a' b')) (C (paired a' b')))
              (ts' a')
              (λ b' → graft K (B (paired a' b')) (C (paired a' b'))
                            (ts (paired a' b')) (tss (paired a' b')))

      -- RHS endpoint of the per-fibre IH at fibre `a'`: the "outer-graft of the
      -- inner-graft" form on the `(B' a' , B ∘ paired a' , C ∘ paired a')` triple,
      -- with continuation `tss ∘ paired a' ∘ ⟦⅀⟧` after one Σ destructuring.
      per-fibre-IH-to : (a' : El A')
                      → FreeOps K (⅀ (B'' a') (⅀Assoc-C' (B' a') (λ b' → B (paired a' b'))
                                                                  (λ b' b'' → C (paired a' b') b'')))
      per-fibre-IH-to a' =
        graft K (⅀ (B' a') (λ b' → B (paired a' b')))
              (⅀Assoc-C' (B' a') (λ b' → B (paired a' b')) (λ b' b'' → C (paired a' b') b''))
              (graft K (B' a') (λ b' → B (paired a' b')) (ts' a') (λ b' → ts (paired a' b')))
              (λ ab → tss (paired a' (fst (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) ab)))
                          (snd (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) ab)))

      -- The per-fibre IH itself — a recursive `graft-assoc` call at fibre `a'`.
      -- This is where the structural induction on the operand tree pays off.
      per-fibre-IH-PathP : (a' : El A')
                        → PathP (λ i → FreeOps K (Inj (⅀Assoc≃ (B' a') (λ b' → B (paired a' b'))
                                                                (λ b' b'' → C (paired a' b') b'')) i))
                                (per-fibre-IH-from a') (per-fibre-IH-to a')
      per-fibre-IH-PathP a' =
        graft-assoc K (B' a') (λ b' → B (paired a' b'))
                    (λ b' b'' → C (paired a' b') b'')
                    (ts' a') (λ b' → ts (paired a' b')) (λ b' b'' → tss (paired a' b') b'')

      -- Per-fibre Code-level path `B-LHS a' ≡ B-RHS a'`: compose the per-fibre
      -- `Inj (⅀Assoc≃ …)` with the `cong (⅀ (B'' a')) (snd-adjust-a' a')`
      -- correction. Used inside `node-path-pre-assoc` via `cong (⅀ A') (funExt …)`.
      per-fibre-Δ : (a' : El A') → B-LHS a' ≡ B-RHS a'
      per-fibre-Δ a' = Inj (⅀Assoc≃ (B' a') (λ b' → B (paired a' b')) (λ b' b'' → C (paired a' b') b''))
                     ∙ cong (⅀ (B'' a')) (snd-adjust-a' a')

      -- Continuation-adjustment (the node-case analog of `tss-eq` in `eq-leaf`):
      -- substing the per-fibre IH's "tss"-continuation along `funExt⁻ (snd-adjust-a')`
      -- recovers the actual RHS-side continuation `tss-curry-top ∘ ⟦⅀⟧ ∘ transp-⅀AB
      -- ∘ invEq ⟦⅀⟧`. Proved by decomposing `snd-adjust-a'` into its two
      -- `C-curry-top`-cong factors, then `substComposite + fromPathP` on each.
      cont-eq-fn : (a' : El A') (b' : El (B'' a'))
                 → subst (FreeOps K) (funExt⁻ (snd-adjust-a' a') b')
                         (tss (paired a' (b'-of a' b')) (c'-of a' b'))
                 ≡ tss-curry-top (equivFun (⟦⅀⟧ (⅀ A' B') B)
                                          (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , b'))))
      cont-eq-fn a' b' =
        let
          body : subst (FreeOps K) (cong C-curry-top (ΣPathP (refl , c'-of-eq a' b'))
                                   ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a' b')))
                       (tss (paired a' (b'-of a' b')) (c'-of a' b'))
               ≡ tss-curry-top (equivFun (⟦⅀⟧ (⅀ A' B') B)
                                          (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , b'))))
          body =
              substComposite (FreeOps K)
                             (cong C-curry-top (ΣPathP (refl , c'-of-eq a' b')))
                             (sym (cong C-curry-top (⟦⅀⟧-on-transp a' b')))
                             (tss (paired a' (b'-of a' b')) (c'-of a' b'))
            ∙ cong (subst (FreeOps K) (sym (cong C-curry-top (⟦⅀⟧-on-transp a' b'))))
                   (fromPathP (cong tss-curry-top (ΣPathP (refl , c'-of-eq a' b'))))
            ∙ fromPathP (cong tss-curry-top (sym (⟦⅀⟧-on-transp a' b')))
        in
          cong (λ p → subst (FreeOps K) p (tss (paired a' (b'-of a' b')) (c'-of a' b')))
               (funExt-⁻∙-eq a' b') ∙ body
        where
          opaque
            unfolding snd-adjust-a'
            funExt-⁻∙-eq : (a' : El A') (b' : El (B'' a'))
                         → funExt⁻ (snd-adjust-a' a') b'
                         ≡ cong C-curry-top (ΣPathP (refl , c'-of-eq a' b'))
                         ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a' b'))
            funExt-⁻∙-eq a' b' = refl

      cont-eq : (a' : El A')
              → (λ b' → subst (FreeOps K) (funExt⁻ (snd-adjust-a' a') b')
                              (tss (paired a' (b'-of a' b')) (c'-of a' b')))
              ≡ (λ b' → tss-curry-top (equivFun (⟦⅀⟧ (⅀ A' B') B)
                                                (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , b')))))
      cont-eq a' = funExt (cont-eq-fn a')

      -- The per-fibre RHS endpoint, exactly as it appears inside `inner-RHS-node`'s
      -- `node` body. Equal to `per-fibre-IH-to a'` modulo `snd-adjust-a'`-rebase
      -- and `cont-eq` continuation-correction.
      per-fibre-RHS-actual : (a' : El A') → FreeOps K (B-RHS a')
      per-fibre-RHS-actual a' =
        graft K (B'' a') (λ b' → C1 (invEq (⟦⅀⟧ A' B'') (a' , b')))
              (graft K (B' a') (λ b' → B (paired a' b')) (ts' a') (λ b' → ts (paired a' b')))
              (λ b' → tss-curry-top (equivFun (⟦⅀⟧ (⅀ A' B') B)
                                              (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , b')))))

      -- Per-fibre `PathP` along the full `per-fibre-Δ a'`. Built as
      -- `compPathP'` of the per-fibre IH (which lands at `per-fibre-IH-to`)
      -- composed with `toPathP step2` (which closes the `cong (⅀ (B'' a'))
      -- (snd-adjust-a' a')` gap via `graft-subst-snd` and `cont-eq`).
      per-fibre-Δ-PathP : (a' : El A')
                       → PathP (λ i → FreeOps K (per-fibre-Δ a' i))
                               (per-fibre-IH-from a') (per-fibre-RHS-actual a')
      per-fibre-Δ-PathP a' = compPathP' {B = FreeOps K} (per-fibre-IH-PathP a') (toPathP step2)
        where
          opaque
            -- Path-valued helper: subst-along-cong-of-snd-adjust on `per-fibre-IH-to`
            -- composes the snd-adjust step with the continuation correction `cont-eq`.
            step2 : subst (FreeOps K) (cong (⅀ (B'' a')) (snd-adjust-a' a')) (per-fibre-IH-to a')
                  ≡ per-fibre-RHS-actual a'
            step2 =
                graft-subst-snd K (B'' a') (snd-adjust-a' a')
                                (graft K (B' a') (λ b' → B (paired a' b')) (ts' a') (λ b' → ts (paired a' b')))
                                (λ ab → tss (paired a' (b'-of a' ab)) (c'-of a' ab))
              ∙ cong (λ f → graft K (B'' a') (λ b' → C1 (invEq (⟦⅀⟧ A' B'') (a' , b')))
                                  (graft K (B' a') (λ b' → B (paired a' b')) (ts' a')
                                         (λ b' → ts (paired a' b'))) f)
                     (cont-eq a')

      -- (d) `node-path-pre-assoc`: heterogeneous path from `inner-LHS-node` to
      -- `inner-RHS-node`, built by varying both the codomain family (via
      -- `per-fibre-Δ`) and the per-fibre subtrees (via `per-fibre-Δ-PathP`).
      node-path-pre-assoc : PathP (λ i → FreeOps K (⅀ A' (λ a' → per-fibre-Δ a' i)))
                                  inner-LHS-node inner-RHS-node
      node-path-pre-assoc i = node A' (λ a' → per-fibre-Δ a' i) k
                                   (λ a' → per-fibre-Δ-PathP a' i)

      -- The two Code-level paths that `bridge-node` will equate. `LHS-path` is
      -- the path consumed by the outer `Inj (⅀Assoc≃ (⅀ A' B') B C)`-transport
      -- on the LHS, after `⅀AssocD A' B' (λ a → ⅀ (B a) (C a))` has been split off.
      LHS-path : ⅀ A' B-LHS ≡ ⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
      LHS-path = ⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a)) ∙ Inj (⅀Assoc≃ (⅀ A' B') B C)

      -- `RHS-path-tail` is the path appearing on the RHS after `graft-subst-fst`
      -- has been pushed across the outer `graft`: an `⅀AssocD A' B'' C1` factor
      -- followed by `⅀-subst-path` rebasing onto `⅀Assoc-C' (⅀ A' B') B C`.
      RHS-path-tail : ⅀ A' B-RHS ≡ ⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
      RHS-path-tail = ⅀AssocD 𝒰 A' B'' C1
                    ∙ ⅀-subst-path (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C)

      -- ----------------------------------------------------------------
      -- bridge-node assembly
      --
      -- Strategy: sandwich the Code-path equality between `sym (InjSec)` and
      -- `InjSec`, reducing it to an equivalence-equality on `cong El`. The
      -- equivalence-equality is then proved pointwise (`equivEq + funExt`).
      -- At every canonical Σ-pair input, both sides reduce to a single
      -- 3-deep Σ-shuffle Σ-form via the §5 Recipe applied at the LHS, RHS,
      -- per-fibre, and outer levels.
      -- ----------------------------------------------------------------

      -- The mid-level family C'-out a b = ⅀ (B (paired a b)) (C (paired a b)).
      -- Used wherever a `B-LHS` index is destructured via `⟦⅀⟧`.
      C'-out : (a : El A') → El (B' a) → Code
      C'-out a b = ⅀ (B (paired a b)) (C (paired a b))

      -- The fst/snd components extracted from `z : El (B-LHS a)` via `⟦⅀⟧`.
      -- Kept because they're referenced in the canonical-form bridge below.
      b-of-LHS : (a : El A') (z : El (B-LHS a)) → El (B' a)
      b-of-LHS a z = fst (equivFun (⟦⅀⟧ (B' a) (C'-out a)) z)

      w-of-LHS : (a : El A') (z : El (B-LHS a)) → El (C'-out a (b-of-LHS a z))
      w-of-LHS a z = snd (equivFun (⟦⅀⟧ (B' a) (C'-out a)) z)

      -- Transport-along-⅀AssocD on canonical pair: a 1-line specialisation of
      -- `transp-⅀AssocD-pair` (§5 toolkit) with γ = λ a → ⅀ (B a) (C a). All
      -- the previous bookkeeping (Assoc-cont-LHS / step-Assoc-on-pair-LHS /
      -- transp-C'-eq-out / key-eq-LHS / c'-of-eq-LHS / Assoc-cont-LHS-explicit /
      -- substed-w-of-LHS / C'-eq-out / transp-C'-eq-out-on-canonical) is now
      -- absorbed by the generic.
      opaque
        transp-⅀AssocD-LHS-on-pair
          : (a : El A') (z : El (B-LHS a))
          → transport (cong El (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a))))
                      (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ≡ invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
                  (paired a (b-of-LHS a z) , w-of-LHS a z)
        transp-⅀AssocD-LHS-on-pair a z =
          transp-⅀AssocD-pair A' B' (λ ab → ⅀ (B ab) (C ab)) a z

      -- The canonical Σ-form both LHS and RHS chains reduce to. Just the
      -- toolkit's `Assoc-cont` at the outer level `(⅀ A' B', B, C)`, applied to
      -- the `paired a (b-of-LHS a z) , w-of-LHS a z` pair. The previous local
      -- `outer-Assoc-cont` / `outer-Assoc-cont-refl` are subsumed by `Assoc-cont`
      -- / `Assoc-cont-at-pair`.
      canonical-form : (a : El A') (z : El (B-LHS a))
                     → El (⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
      canonical-form a z =
        Assoc-cont (⅀ A' B') B C (paired a (b-of-LHS a z) , w-of-LHS a z)

      -- LHS-side reduction at a canonical Σ-pair input. Mirrors `LHS-chain` of
      -- the leaf case: split `LHS-path` with `congFunct + substComposite`, apply
      -- `transp-⅀AssocD-LHS-on-pair` to the inner `⅀AssocD`-leg, then `step-Assoc-on-pair`
      -- to the outer `Inj (⅀Assoc≃ (⅀ A' B') B C)`-leg.
      opaque
        LHS-chain-on-pair
          : (a : El A') (z : El (B-LHS a))
          → transport (cong El LHS-path) (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ≡ canonical-form a z
        LHS-chain-on-pair a z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
                 (congFunct El (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a)))
                                (Inj (⅀Assoc≃ (⅀ A' B') B C)))
          ∙ substComposite (λ X → X)
                           (cong El (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a))))
                           (cong El (Inj (⅀Assoc≃ (⅀ A' B') B C)))
                           (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ∙ cong (transport (cong El (Inj (⅀Assoc≃ (⅀ A' B') B C))))
                 (transp-⅀AssocD-LHS-on-pair a z)
          ∙ step-Assoc-on-pair (⅀ A' B') B C
                               (paired a (b-of-LHS a z) , w-of-LHS a z)

      -- Extend `LHS-chain-on-pair` from canonical-pair inputs to arbitrary
      -- `x : El (⅀ A' B-LHS)` by `retEq (⟦⅀⟧ A' B-LHS) x` (`x ≡ invEq ⟦⅀⟧
      -- (equivFun ⟦⅀⟧ x)`).
      a-of-x : El (⅀ A' B-LHS) → El A'
      a-of-x x = fst (equivFun (⟦⅀⟧ A' B-LHS) x)

      z-of-x : (x : El (⅀ A' B-LHS)) → El (B-LHS (a-of-x x))
      z-of-x x = snd (equivFun (⟦⅀⟧ A' B-LHS) x)

      opaque
        LHS-chain-node
          : (x : El (⅀ A' B-LHS))
          → transport (cong El LHS-path) x
          ≡ canonical-form (a-of-x x) (z-of-x x)
        LHS-chain-node x =
            cong (transport (cong El LHS-path)) (sym (retEq (⟦⅀⟧ A' B-LHS) x))
          ∙ LHS-chain-on-pair (a-of-x x) (z-of-x x)

      -- ----------------------------------------------------------------
      -- RHS chain
      -- ----------------------------------------------------------------

      -- Intermediate family for `⅀AssocD A' B'' C1`: `C1'-out a b` is `C1`
      -- evaluated at the canonical Σ-pre-image.
      C1'-out : (a : El A') → El (B'' a) → Code
      C1'-out a b = C1 (invEq (⟦⅀⟧ A' B'') (a , b))

      -- The fst/snd components extracted from `z : El (B-RHS a)` via `⟦⅀⟧`.
      -- Kept because they're referenced in `RHS-chain-on-pair` below.
      b-of-RHS : (a : El A') (z : El (B-RHS a)) → El (B'' a)
      b-of-RHS a z = fst (equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) z)

      w-of-RHS : (a : El A') (z : El (B-RHS a)) → El (C1'-out a (b-of-RHS a z))
      w-of-RHS a z = snd (equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) z)

      -- Transport-along-⅀AssocD on canonical pair for the RHS side: a 1-line
      -- specialisation of `transp-⅀AssocD-pair` (§5 toolkit) with γ = C1.
      -- The previous bookkeeping for Assoc-cont-RHS / step-Assoc-on-pair-RHS /
      -- transp-C1'-eq-out / key-eq-RHS / c'-of-eq-RHS / Assoc-cont-RHS-explicit /
      -- substed-w-of-RHS / C1'-eq-out / transp-C1'-eq-out-on-canonical is now
      -- absorbed by the generic.
      opaque
        transp-⅀AssocD-RHS-on-pair
          : (a : El A') (z : El (B-RHS a))
          → transport (cong El (⅀AssocD 𝒰 A' B'' C1)) (invEq (⟦⅀⟧ A' B-RHS) (a , z))
          ≡ invEq (⟦⅀⟧ (⅀ A' B'') C1)
                  (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , w-of-RHS a z)
        transp-⅀AssocD-RHS-on-pair a z = transp-⅀AssocD-pair A' B'' C1 a z

      -- ----------------------------------------------------------------
      -- Per-fibre Σ-shuffle (used to compute transport along `per-fibre-Δ`)
      --
      -- At the per-fibre level, the toolkit's `Assoc-cont` and `step-Assoc-on-pair`
      -- are instantiated with `(A := B' a , B := λ b' → B (paired a b') , C := λ b' b'' →
      -- C (paired a b') b'')`. The previous local `Assoc-cont-per-fibre` etc. are
      -- all subsumed; the only surviving locals are the `b''-of` / `c''-of` /
      -- `shifted-c''-per-fibre` destructurings of a `w : El (C'-out a b)` value.
      -- ----------------------------------------------------------------

      -- Destructure `w : El (C'-out a b) = El (⅀ (B (paired a b)) (C (paired a b)))`
      -- via `⟦⅀⟧ (B (paired a b)) (C (paired a b))`.
      b''-of : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
             → El (B (paired a b))
      b''-of a b w = fst (equivFun (⟦⅀⟧ (B (paired a b)) (C (paired a b))) w)

      c''-of : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
             → El (C (paired a b) (b''-of a b w))
      c''-of a b w = snd (equivFun (⟦⅀⟧ (B (paired a b)) (C (paired a b))) w)

      -- The `subst`-shifted `c`-component arising inside the per-fibre
      -- `Assoc-cont` at canonical pair `(b , w)`. Analog of `substed-c-of` at the
      -- per-fibre level.
      shifted-c''-per-fibre
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                (λ b' b'' → C (paired a b') b'')
                                 (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)))
      shifted-c''-per-fibre a b w =
        subst (λ p → El (C (paired a (fst p)) (snd p)))
              (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)))
              (c''-of a b w)

      -- ----------------------------------------------------------------
      -- R1: transport via `cong (⅀ A') (funExt per-fibre-Δ)`. This is the
      -- per-fibre Σ-shuffle, "lifted" to a snd-component of the outer Σ.
      -- ----------------------------------------------------------------

      -- The "inner" `snd`-component of `transport (cong El (per-fibre-Δ a))` on a
      -- canonical `invEq ⟦⅀⟧ (b , w)` input, before identifying it with `R1-snd-form`.
      R1-snd-on-pair : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
                     → El (B-RHS a)
      R1-snd-on-pair a b w =
        transport (cong El (per-fibre-Δ a)) (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))

      -- The canonical Σ-pair shape that `R1-snd-on-pair` reduces to: `invEq ⟦⅀⟧`
      -- of `(invEq ⟦⅀⟧ (b , b''-of a b w) , transport-along-snd-adjust …
      -- (shifted-c''-per-fibre …))`.
      R1-snd-form
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (B-RHS a)
      R1-snd-form a b w =
        invEq (⟦⅀⟧ (B'' a) (C1'-out a))
              ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
              , transport (cong El (funExt⁻ (snd-adjust-a' a)
                                              (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
                          (shifted-c''-per-fibre a b w))

      -- Identify `R1-snd-on-pair` with `R1-snd-form`. Mirrors `LHS-chain-on-pair`
      -- at the per-fibre level: split `per-fibre-Δ` with `congFunct`/`substComposite`,
      -- apply `step-Assoc-on-pair` to the `Inj (⅀Assoc≃ …)`-leg, then use
      -- `⟦⅀⟧-natural-snd` + `secEq` for the `cong (⅀ (B'' a)) (snd-adjust-a' a)`-leg.
      opaque
        R1-snd-on-pair-eq
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → R1-snd-on-pair a b w ≡ R1-snd-form a b w
        R1-snd-on-pair-eq a b w =
            cong (λ p → transport p (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w)))
                 (congFunct El (Inj (⅀Assoc≃ (B' a) (λ b' → B (paired a b'))
                                                      (λ b' b'' → C (paired a b') b'')))
                                (cong (⅀ (B'' a)) (snd-adjust-a' a)))
          ∙ substComposite (λ X → X)
                           (cong El (Inj (⅀Assoc≃ (B' a) (λ b' → B (paired a b'))
                                                           (λ b' b'' → C (paired a b') b''))))
                           (cong El (cong (⅀ (B'' a)) (snd-adjust-a' a)))
                           (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
          ∙ cong (transport (cong (λ B''' → El (⅀ (B'' a) B''')) (snd-adjust-a' a)))
                 (step-Assoc-on-pair (B' a) (λ b' → B (paired a b'))
                                            (λ b' b'' → C (paired a b') b'')
                                            (b , w))
          ∙ cong (λ e → equivFun e (invEq (⟦⅀⟧ (B'' a) (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                                                          (λ b' b'' → C (paired a b') b'')))
                                           ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
                                           , shifted-c''-per-fibre a b w)))
                 (⟦⅀⟧-natural-snd 𝒰 (B'' a) (snd-adjust-a' a))
          ∙ cong (λ p → invEq (⟦⅀⟧ (B'' a) (C1'-out a))
                              (fst p ,
                               transport (cong El (funExt⁻ (snd-adjust-a' a) (fst p))) (snd p)))
                 (secEq (⟦⅀⟧ (B'' a) (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                                          (λ b' b'' → C (paired a b') b'')))
                        ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
                        , shifted-c''-per-fibre a b w))

      -- `R1` lifted to the outer Σ: `transport (cong (⅀ A') (funExt per-fibre-Δ))`
      -- of an `invEq ⟦⅀⟧ (a , z)` recovers `invEq ⟦⅀⟧ (a , transport-along-per-fibre-Δ z)`.
      -- Direct application of `⟦⅀⟧-natural-snd` followed by `secEq`.
      opaque
        R1-on-pair
          : (a : El A') (z : El (B-LHS a))
          → transport (cong (λ B''' → El (⅀ A' B''')) (funExt per-fibre-Δ))
                      (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ≡ invEq (⟦⅀⟧ A' B-RHS) (a , transport (cong El (per-fibre-Δ a)) z)
        R1-on-pair a z =
            cong (λ e → equivFun e (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
                 (⟦⅀⟧-natural-snd 𝒰 A' (funExt per-fibre-Δ))
          ∙ cong (λ p → invEq (⟦⅀⟧ A' B-RHS)
                              (fst p ,
                               transport (cong El (funExt⁻ (funExt per-fibre-Δ) (fst p))) (snd p)))
                 (secEq (⟦⅀⟧ A' B-LHS) (a , z))

      -- ----------------------------------------------------------------
      -- RHS-form: the canonical Σ-shape that `RHS-chain-on-pair` lands in.
      -- ----------------------------------------------------------------

      -- The natural endpoint of the RHS chain at a canonical pair `(a , z)`:
      -- `invEq ⟦⅀⟧` of the pair `(transp-⅀AB (invEq ⟦⅀⟧ (a , b-of-RHS …)) , w-of-RHS …)`
      -- where the RHS-side `b`/`w` are extracted from `transport-along-per-fibre-Δ z`.
      RHS-form : (a : El A') (z : El (B-LHS a))
               → El (⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
      RHS-form a z =
        invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
              ( transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a (transport (cong El (per-fibre-Δ a)) z)))
              , w-of-RHS a (transport (cong El (per-fibre-Δ a)) z))

      -- RHS-side reduction at a canonical Σ-pair input. Three-stage chain:
      --   1. Split `cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail` with
      --      `congFunct`/`substComposite`, then apply `R1-on-pair` to the
      --      first leg.
      --   2. Split `RHS-path-tail = ⅀AssocD … ∙ ⅀-subst-path …` similarly, apply
      --      `transp-⅀AssocD-RHS-on-pair` to the `⅀AssocD`-leg.
      --   3. `transp-⅀-subst-path` handles the `⅀-subst-path` leg; a final
      --      `secEq` cancels the inner `equivFun ⟦⅀⟧ ∘ invEq ⟦⅀⟧`.
      opaque
        RHS-chain-on-pair
          : (a : El A') (z : El (B-LHS a))
          → transport (cong El (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail))
                      (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ≡ RHS-form a z
        RHS-chain-on-pair a z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
                 (congFunct El (cong (⅀ A') (funExt per-fibre-Δ)) RHS-path-tail)
          ∙ substComposite (λ X → X)
                           (cong El (cong (⅀ A') (funExt per-fibre-Δ)))
                           (cong El RHS-path-tail)
                           (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ∙ cong (transport (cong El RHS-path-tail)) (R1-on-pair a z)
          ∙ cong (λ p → transport p (invEq (⟦⅀⟧ A' B-RHS) (a , transport (cong El (per-fibre-Δ a)) z)))
                 (congFunct El (⅀AssocD 𝒰 A' B'' C1)
                                (⅀-subst-path (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C)))
          ∙ substComposite (λ X → X)
                           (cong El (⅀AssocD 𝒰 A' B'' C1))
                           (cong El (⅀-subst-path (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C)))
                           (invEq (⟦⅀⟧ A' B-RHS) (a , transport (cong El (per-fibre-Δ a)) z))
          ∙ cong (transport (cong El (⅀-subst-path (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C))))
                 (transp-⅀AssocD-RHS-on-pair a (transport (cong El (per-fibre-Δ a)) z))
          ∙ transp-⅀-subst-path (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C)
                                 (invEq (⟦⅀⟧ (⅀ A' B'') C1)
                                         ( invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a (transport (cong El (per-fibre-Δ a)) z))
                                         , w-of-RHS a (transport (cong El (per-fibre-Δ a)) z)))
          ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
                              ( transp-⅀AB (fst p) , snd p ))
                 (secEq (⟦⅀⟧ (⅀ A' B'') C1)
                        ( invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a (transport (cong El (per-fibre-Δ a)) z))
                        , w-of-RHS a (transport (cong El (per-fibre-Δ a)) z)))

      -- ----------------------------------------------------------------
      -- Connecting `RHS-form` to `canonical-form` (the node-case σ-bridge)
      -- ----------------------------------------------------------------

      -- Convenience: `b''-of` and `c''-of` reapplied with the canonical
      -- destructurings of an arbitrary `z : El (B-LHS a)`.
      b''-of-z : (a : El A') (z : El (B-LHS a)) → El (B (paired a (b-of-LHS a z)))
      b''-of-z a z = b''-of a (b-of-LHS a z) (w-of-LHS a z)

      c''-of-z : (a : El A') (z : El (B-LHS a))
               → El (C (paired a (b-of-LHS a z)) (b''-of-z a z))
      c''-of-z a z = c''-of a (b-of-LHS a z) (w-of-LHS a z)

      -- The "shifted" `c''`-component at the outer Σ-level: `subst` of `c''-of`
      -- along `sym (secEq ⟦⅀⟧ (⅀ A' B') B (paired a b , b''-of a b w))`. The
      -- outermost analog of `substed-c-of` and `shifted-c''-per-fibre`.
      shifted-c''-outer
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (⅀Assoc-C' (⅀ A' B') B C
                         (invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)))
      shifted-c''-outer a b w =
        subst (λ p → El (C (fst p) (snd p)))
              (sym (secEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)))
              (c''-of a b w)

      -- `shifted-c''-outer` reapplied at the canonical destructurings of `z`.
      shifted-c''-outer-z
        : (a : El A') (z : El (B-LHS a))
        → El (⅀Assoc-C' (⅀ A' B') B C
                         (invEq (⟦⅀⟧ (⅀ A' B') B) (paired a (b-of-LHS a z) , b''-of-z a z)))
      shifted-c''-outer-z a z = shifted-c''-outer a (b-of-LHS a z) (w-of-LHS a z)

      -- `canonical-form a z` definitionally unfolds (through `Assoc-cont`'s
      -- five-fold Σ-shuffle) to the explicit `invEq ⟦⅀⟧ … (invEq ⟦⅀⟧ … ,
      -- shifted-c''-outer-z …)` form. Recorded with `refl` so consumers can
      -- `cong`-rewrite under this shape.
      canonical-form-explicit
        : (a : El A') (z : El (B-LHS a))
        → canonical-form a z
        ≡ invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
                ( invEq (⟦⅀⟧ (⅀ A' B') B) (paired a (b-of-LHS a z) , b''-of-z a z)
                , shifted-c''-outer-z a z)
      canonical-form-explicit _ _ = refl

      -- `transp-⅀AB` on a doubly-canonical pair `(a , invEq ⟦⅀⟧ (b , b''))`
      -- recovers `invEq ⟦⅀⟧ (paired a b , b'')`. The node-case analog of
      -- `transp-⅀IdlD` used in the leaf case's `σ-bridge`. Built by `transp-⅀AB-factored`
      -- followed by `transp-C'-eq-on-canonical`, with a `c'-of-eq`-driven `ΣPathP`
      -- and a final `secEq` to align the `subst` shape with the canonical form.
      opaque
        transp-⅀AssocD-on-canonical
          : (a : El A') (b : El (B' a)) (b'' : El (B (paired a b)))
          → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b'')))
          ≡ invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b'')
        transp-⅀AssocD-on-canonical a b b'' =
            transp-⅀AB-factored a (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))
          ∙ transp-C'-eq-on-canonical a (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))
          ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') B) (paired a (fst p) , snd p))
                 ( ΣPathP (refl ,
                            sym (c'-of-eq a (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))))
                 ∙ secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))

      -- `equivFun ⟦⅀⟧ ∘ R1-snd-form` recovers its underlying Σ-pair via `secEq`.
      -- Used to bridge `R1-snd-on-pair-eq` (which lands in `R1-snd-form`) with
      -- the Σ-shape consumed by `Σ-bridge-fst`.
      opaque
        ⟦⅀⟧-on-R1-snd-form
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) (R1-snd-form a b w)
          ≡ ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
            , transport (cong El (funExt⁻ (snd-adjust-a' a)
                                            (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
                        (shifted-c''-per-fibre a b w))
        ⟦⅀⟧-on-R1-snd-form a b w =
          secEq (⟦⅀⟧ (B'' a) (C1'-out a))
                ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
                , transport (cong El (funExt⁻ (snd-adjust-a' a)
                                                (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
                            (shifted-c''-per-fibre a b w))

      -- ----------------------------------------------------------------
      -- σ-bridge: `canonical-form a z ≡ RHS-form a z` on canonical pair input.
      -- Node-case analog of the leaf-case `σ-bridge`.
      -- ----------------------------------------------------------------

      -- Σ-pair shape of `Assoc-cont (⅀ A' B') B C (paired a b , w)`: a `refl`
      -- recording of how the toolkit's `Assoc-cont` unfolds at this specific
      -- input. Used to rewrite the LHS of `σ-bridge-on-pair` into a form whose
      -- `fst`/`snd` components can be paired separately via `Σ-bridge-fst`/`Σ-bridge-snd-…`.
      canonical-form-on-pair-Σ
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → Assoc-cont (⅀ A' B') B C (paired a b , w)
        ≡ invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
                ( invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)
                , shifted-c''-outer a b w)
      canonical-form-on-pair-Σ _ _ _ = refl

      -- `equivFun ⟦⅀⟧ (R1-snd-on-pair …)` in canonical Σ-pair form. Chain
      -- `R1-snd-on-pair-eq` (which lands in `R1-snd-form`) with `⟦⅀⟧-on-R1-snd-form`
      -- (which extracts its underlying Σ-pair).
      opaque
        path1
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) (R1-snd-on-pair a b w)
          ≡ ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
            , transport (cong El (funExt⁻ (snd-adjust-a' a)
                                            (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
                        (shifted-c''-per-fibre a b w))
        path1 a b w =
            cong (equivFun (⟦⅀⟧ (B'' a) (C1'-out a))) (R1-snd-on-pair-eq a b w)
          ∙ ⟦⅀⟧-on-R1-snd-form a b w

      -- `fst`-leg of the Σ-bridge: identifies the `fst`-component of
      -- `canonical-form a (invEq ⟦⅀⟧ (b , w))` with the `fst`-component of
      -- `RHS-form a (invEq ⟦⅀⟧ (b , w))`. Composes `sym (transp-⅀AssocD-on-canonical …)`
      -- with a `cong (transp-⅀AB ∘ invEq ⟦⅀⟧ ∘ (a , _))` of `sym (cong fst path1)`.
      opaque
        Σ-bridge-fst
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)
          ≡ transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a (R1-snd-on-pair a b w)))
        Σ-bridge-fst a b w =
            sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))
          ∙ cong (λ x → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , x)))
                 (sym (cong fst (path1 a b w)))

      -- Midpoint of `Σ-bridge-fst`: the `snd`-component at the intermediate
      -- shape `transp-⅀AB (invEq ⟦⅀⟧ (a , invEq ⟦⅀⟧ (b , b''-of a b w)))`.
      Σ-bridge-mid-snd
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (⅀Assoc-C' (⅀ A' B') B C
                          (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)))))
      Σ-bridge-mid-snd a b w =
        transport (cong El (funExt⁻ (snd-adjust-a' a)
                                      (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
                  (shifted-c''-per-fibre a b w)

      -- Second leg of the Σ-bridge `snd`-component: heterogeneous path from
      -- `Σ-bridge-mid-snd` to `w-of-RHS (R1-snd-on-pair …)`, varying along
      -- `cong (transp-⅀AB ∘ invEq ⟦⅀⟧ ∘ (a , _)) (sym (cong fst (path1 …)))`.
      -- Built directly as `λ i → snd (path1 (~ i))`.
      opaque
        Σ-bridge-snd-part2
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → PathP (λ i → El (⅀Assoc-C' (⅀ A' B') B C
                                          (transp-⅀AB (invEq (⟦⅀⟧ A' B'')
                                                              (a , cong fst (path1 a b w) (~ i))))))
                  (Σ-bridge-mid-snd a b w)
                  (w-of-RHS a (R1-snd-on-pair a b w))
        Σ-bridge-snd-part2 a b w = λ i → snd (path1 a b w (~ i))

      -- Unfold `funExt⁻ (snd-adjust-a' a) z'` along the definition of
      -- `snd-adjust-a'` as a `funExt` of a 2-factor `∙`-composition. Recorded
      -- with `refl` (after `unfolding snd-adjust-a'`) so consumers can rewrite
      -- under this shape without paying a propositional step.
      opaque
        unfolding snd-adjust-a'
        snd-adjust-on-pair-decomp
          : (a : El A') (z' : El (B'' a))
          → funExt⁻ (snd-adjust-a' a) z'
          ≡ cong C-curry-top (ΣPathP (refl , c'-of-eq a z'))
          ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a z'))
        snd-adjust-on-pair-decomp _ _ = refl

      -- Code-level path equality consumed by `Σ-bridge-snd-part1-endpoint` below.
      -- The node-level analog of the leaf case's `funExt-q-decomp`. Both sides
      -- factor as `cong C-curry-top` of paths in `Σ (El (⅀ A' B')) (λ ab → El (B ab))`;
      -- the inner Σ-level equation closes via a single `homotopyNatural` application
      -- against `secEq ⟦⅀⟧ (⅀ A' B') B`, with the three constituent steps of
      -- `transp-⅀AssocD-on-canonical` cancelling against `⟦⅀⟧-on-transp` modulo
      -- one `homotopyNatural`-driven `secEq` rearrangement.
      opaque
        unfolding transp-⅀AssocD-on-canonical snd-adjust-a' transp-⅀AB-factored transp-C'-eq-on-canonical ⟦⅀⟧-on-transp
        path-bridge-LHS-to-RHS
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → ( cong (λ p → C (fst p) (snd p))
                   (sym (secEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)))
            ∙ cong (⅀Assoc-C' (⅀ A' B') B C)
                   (sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))) )
          ≡ ( cong (λ p → C (paired a (fst p)) (snd p))
                   (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)))
            ∙ funExt⁻ (snd-adjust-a' a)
                       (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)) )
        path-bridge-LHS-to-RHS a b w =
          let
            ⟦⅀⟧'  = ⟦⅀⟧ (⅀ A' B') B
            ⟦⅀⟧'' = ⟦⅀⟧ (B' a) (λ b' → B (paired a b'))
            z'    : El (B'' a)
            z'    = invEq ⟦⅀⟧'' (b , b''-of a b w)
            secO  = secEq ⟦⅀⟧' (paired a b , b''-of a b w)
            secF  = secEq ⟦⅀⟧'' (b , b''-of a b w)
            M     : Σ (El (⅀ A' B')) (λ ab → El (B ab))
            M     = paired a (b'-of a z')
                  , transport (cong El (funExt⁻ C'-eq (paired a (b'-of a z'))))
                              (substed-c-of a z')
            secM  = secEq ⟦⅀⟧' M

            pfs : Σ (El (B' a)) (λ b' → El (B (paired a b')))
                → Σ (El (⅀ A' B')) (λ ab → El (B ab))
            pfs p = paired a (fst p) , snd p

            Q1 : Path (Σ (El (B' a)) (λ b' → El (B (paired a b'))))
                     ( b'-of a z'
                     , transport (cong El (funExt⁻ C'-eq (paired a (b'-of a z'))))
                                 (substed-c-of a z') )
                     ( b'-of a z' , c'-of a z' )
            Q1 = ΣPathP (refl , sym (c'-of-eq a z'))
            P  = Q1 ∙ secF

            -- TAC's three constituent paths (as expressed in the body of
            -- transp-⅀AssocD-on-canonical, which is unfolded here).
            -- Post-§5-toolkit refactor: the old `step2 = cong transp-C'-eq
            -- (Assoc-cont-explicit a z')` step has been absorbed into the
            -- definitional equality of `Assoc-cont A' B' C-int` with its
            -- invEq form, so `step123` is now just `step1 ∙ step3`.
            step1 = transp-⅀AB-factored a z'
            step3 = transp-C'-eq-on-canonical a z'
            step4 = cong (λ p → invEq ⟦⅀⟧' (paired a (fst p) , snd p)) P
            step123 = step1 ∙ step3

            TAC = transp-⅀AssocD-on-canonical a b (b''-of a b w)

            -- Homotopy `equivFun ⟦⅀⟧' ∘ invEq ⟦⅀⟧' ∘ pfs ~ pfs`.
            H-pfs : (p : Σ (El (B' a)) (λ b' → El (B (paired a b'))))
                  → equivFun ⟦⅀⟧' (invEq ⟦⅀⟧' (pfs p)) ≡ pfs p
            H-pfs p = secEq ⟦⅀⟧' (pfs p)

            -- (1) Reassociate TAC as step123 ∙ step4.
            --     TAC unfolds to step1 ∙ (step3 ∙ step4) (right-assoc).
            TAC-rearrange : TAC ≡ step123 ∙ step4
            TAC-rearrange = assoc step1 step3 step4

            -- (2) sym (cong (equivFun ⟦⅀⟧') step123) ≡ secM ∙ sym (⟦⅀⟧-on-transp a z').
            --     Uses that ⟦⅀⟧-on-transp a z' = cong (equivFun ⟦⅀⟧') step123 ∙ secM
            --     (definitionally, under unfolding ⟦⅀⟧-on-transp).
            sym-cong-step123
              : sym (cong (equivFun ⟦⅀⟧') step123)
              ≡ secM ∙ sym (⟦⅀⟧-on-transp a z')
            sym-cong-step123 = sym (
                cong (secM ∙_) (symDistr (cong (equivFun ⟦⅀⟧') step123) secM)
              ∙ assoc secM (sym secM) (sym (cong (equivFun ⟦⅀⟧') step123))
              ∙ cong (_∙ sym (cong (equivFun ⟦⅀⟧') step123)) (lCancel (sym secM))
              ∙ sym (lUnit (sym (cong (equivFun ⟦⅀⟧') step123))) )

            -- (3) cong (equivFun ⟦⅀⟧') (sym TAC) factors out an `⟦⅀⟧-on-transp` chunk.
            cong-e-sym-TAC
              : cong (equivFun ⟦⅀⟧') (sym TAC)
              ≡ sym (cong (equivFun ⟦⅀⟧') step4) ∙ secM ∙ sym (⟦⅀⟧-on-transp a z')
            cong-e-sym-TAC =
                cong (λ p → cong (equivFun ⟦⅀⟧') (sym p)) TAC-rearrange
              ∙ cong (cong (equivFun ⟦⅀⟧')) (symDistr step123 step4)
              ∙ congFunct (equivFun ⟦⅀⟧') (sym step4) (sym step123)
              ∙ cong (sym (cong (equivFun ⟦⅀⟧') step4) ∙_) sym-cong-step123

            -- (4) The Σ-level path-of-paths equation: closure via homotopyNatural.
            Σ-eq
              : sym secO ∙ cong (equivFun ⟦⅀⟧') (sym TAC)
              ≡ cong pfs (sym secF) ∙ ΣPathP (refl , c'-of-eq a z')
                                    ∙ sym (⟦⅀⟧-on-transp a z')
            Σ-eq =
                cong (sym secO ∙_) cong-e-sym-TAC
                -- sym secO ∙ (sym (cong e step4) ∙ (secM ∙ sym ⟦⅀⟧-on-transp))
              ∙ cong (sym secO ∙_)
                     (assoc (sym (cong (equivFun ⟦⅀⟧') step4))
                            secM (sym (⟦⅀⟧-on-transp a z')))
                -- sym secO ∙ ((sym (cong e step4) ∙ secM) ∙ sym ⟦⅀⟧-on-transp)
              ∙ cong (λ q → sym secO ∙ (q ∙ sym (⟦⅀⟧-on-transp a z')))
                     (sym (homotopyNatural H-pfs (sym P)))
                -- sym secO ∙ ((secO ∙ cong pfs (sym P)) ∙ sym ⟦⅀⟧-on-transp)
              ∙ assoc (sym secO) (secO ∙ cong pfs (sym P)) (sym (⟦⅀⟧-on-transp a z'))
                -- (sym secO ∙ (secO ∙ cong pfs (sym P))) ∙ sym ⟦⅀⟧-on-transp
              ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z'))
                     (assoc (sym secO) secO (cong pfs (sym P)))
                -- ((sym secO ∙ secO) ∙ cong pfs (sym P)) ∙ sym ⟦⅀⟧-on-transp
              ∙ cong (λ q → (q ∙ cong pfs (sym P)) ∙ sym (⟦⅀⟧-on-transp a z'))
                     (lCancel secO)
                -- (refl ∙ cong pfs (sym P)) ∙ sym ⟦⅀⟧-on-transp
              ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z')) (sym (lUnit (cong pfs (sym P))))
                -- cong pfs (sym P) ∙ sym ⟦⅀⟧-on-transp
              ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z')) (cong (cong pfs) (symDistr Q1 secF))
                -- cong pfs (sym secF ∙ sym Q1) ∙ sym ⟦⅀⟧-on-transp
                -- sym Q1 ≡ ΣPathP (refl , c'-of-eq a z')  is definitional.
              ∙ cong (_∙ sym (⟦⅀⟧-on-transp a z'))
                     (congFunct pfs (sym secF) (ΣPathP (refl , c'-of-eq a z')))
                -- (cong pfs (sym secF) ∙ cong pfs (ΣPathP (refl, c'-of-eq))) ∙ sym ⟦⅀⟧-on-transp
                -- cong pfs (ΣPathP refl q) ≡ ΣPathP refl q  is definitional (outer Σ).
              ∙ sym (assoc (cong pfs (sym secF))
                           (ΣPathP (refl , c'-of-eq a z'))
                           (sym (⟦⅀⟧-on-transp a z')))
                -- cong pfs (sym secF) ∙ (ΣPathP (refl, c'-of-eq) ∙ sym ⟦⅀⟧-on-transp)
          in
            -- Outer wrap: factor cong C-curry-top on both sides, then apply Σ-eq.
              sym (congFunct C-curry-top (sym secO) (cong (equivFun ⟦⅀⟧') (sym TAC)))
              -- cong C-curry-top (sym secO ∙ cong e (sym TAC))
            ∙ cong (cong C-curry-top) Σ-eq
              -- cong C-curry-top (cong pfs (sym secF) ∙ ΣPathP (refl, c'-of-eq) ∙ sym ⟦⅀⟧-on-transp)
            ∙ congFunct C-curry-top (cong pfs (sym secF))
                                    (ΣPathP (refl , c'-of-eq a z')
                                     ∙ sym (⟦⅀⟧-on-transp a z'))
              -- cong C-curry-top (cong pfs (sym secF))
              --   ∙ cong C-curry-top (ΣPathP (refl, c'-of-eq) ∙ sym ⟦⅀⟧-on-transp)
            ∙ cong (cong C-curry-top (cong pfs (sym secF)) ∙_)
                   (congFunct C-curry-top (ΣPathP (refl , c'-of-eq a z'))
                                          (sym (⟦⅀⟧-on-transp a z')))
              -- cong C-curry-top (cong pfs (sym secF))
              --   ∙ (cong C-curry-top (ΣPathP (refl, c'-of-eq))
              --     ∙ cong C-curry-top (sym ⟦⅀⟧-on-transp))
              -- ≡ RHS goal, since cong C-curry-top (sym p) ≡ sym (cong C-curry-top p)
              --   and cong C-curry-top ∘ pfs ≡ λ p → C (paired a (fst p)) (snd p)
              --   are both definitional.

      -- First leg of the Σ-bridge `snd`-component: endpoint-fix. Mirror of the
      -- leaf case's `endpoint-fix` (inside `snd-PathP`), but one Σ-level up: it
      -- takes the outer `shifted-c''-outer` and produces `Σ-bridge-mid-snd` by
      -- a 5-step substComposite/`path-bridge-LHS-to-RHS`/substComposite chain
      -- that swaps the LHS-side Code path for the RHS-side one.
      opaque
        Σ-bridge-snd-part1-endpoint
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → transport (cong (λ x → El (⅀Assoc-C' (⅀ A' B') B C x))
                             (sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))))
                      (shifted-c''-outer a b w)
          ≡ Σ-bridge-mid-snd a b w
        Σ-bridge-snd-part1-endpoint a b w =
            -- Step 1: combine the outer subst from shifted-c''-outer with the
            -- outer transport into a single transport along (path1 ∙ path2).
            sym (substComposite (λ X → X)
                                (cong (λ p → El (C (fst p) (snd p)))
                                      (sym (secEq (⟦⅀⟧ (⅀ A' B') B)
                                                   (paired a b , b''-of a b w))))
                                (cong (λ x → El (⅀Assoc-C' (⅀ A' B') B C x))
                                      (sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))))
                                (c''-of a b w))
            -- Step 2: recognize the composed path as cong El of a Code composition.
          ∙ cong (λ p → transport p (c''-of a b w))
                 (sym (congFunct El
                        (cong (λ p → C (fst p) (snd p))
                              (sym (secEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w))))
                        (cong (⅀Assoc-C' (⅀ A' B') B C)
                              (sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))))))
            -- Step 3: swap to the RHS-style Code path via path-bridge-LHS-to-RHS.
          ∙ cong (λ p → transport (cong El p) (c''-of a b w))
                 (path-bridge-LHS-to-RHS a b w)
            -- Step 4: unfold cong El back into a composition on the RHS side.
          ∙ cong (λ p → transport p (c''-of a b w))
                 (congFunct El
                    (cong (λ p → C (paired a (fst p)) (snd p))
                          (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                       (b , b''-of a b w))))
                    (funExt⁻ (snd-adjust-a' a)
                              (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
            -- Step 5: split back into substComposite (inverse of Step 1, on RHS path).
          ∙ substComposite (λ X → X)
                           (cong (λ p → El (C (paired a (fst p)) (snd p)))
                                 (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                              (b , b''-of a b w))))
                           (cong El (funExt⁻ (snd-adjust-a' a)
                                                (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b')))
                                                        (b , b''-of a b w))))
                           (c''-of a b w)

      -- ----------------------------------------------------------------
      -- bridge-node assembly (standard `InjSec` sandwich)
      -- ----------------------------------------------------------------

      -- On a canonical pair input `(invEq ⟦⅀⟧ (b , w))`, `canonical-form` (i.e.
      -- the LHS-side Σ-shape) coincides with `RHS-form` (the RHS-side Σ-shape).
      -- Built from `Σ-bridge-fst` (the `fst`-leg) and a `compPathP'` of
      -- `Σ-bridge-snd-part1-endpoint` and `Σ-bridge-snd-part2` for the `snd`-leg.
      opaque
        unfolding Σ-bridge-fst
        σ-bridge-on-pair
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → Assoc-cont (⅀ A' B') B C (paired a b , w)
          ≡ RHS-form a (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
        σ-bridge-on-pair a b w =
          cong (invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)))
               (ΣPathP (Σ-bridge-fst a b w
                       , compPathP' {B = λ x → El (⅀Assoc-C' (⅀ A' B') B C x)}
                                    (toPathP (Σ-bridge-snd-part1-endpoint a b w))
                                    (Σ-bridge-snd-part2 a b w)))

      -- Lift `σ-bridge-on-pair` from canonical-pair inputs to arbitrary
      -- `z : El (B-LHS a)` by `retEq (⟦⅀⟧ (B' a) (C'-out a)) z`.
      opaque
        σ-bridge-base
          : (a : El A') (z : El (B-LHS a))
          → canonical-form a z ≡ RHS-form a z
        σ-bridge-base a z =
            σ-bridge-on-pair a (b-of-LHS a z) (w-of-LHS a z)
          ∙ cong (RHS-form a) (retEq (⟦⅀⟧ (B' a) (C'-out a)) z)

      -- The heart of the node-case bridge: at every `x : El (⅀ A' B-LHS)`, the
      -- LHS and RHS Code-paths transport `x` to the same thing. Lifts
      -- `σ-bridge-base` from a canonical Σ-pair input to arbitrary `x` via
      -- two `retEq` applications.
      opaque
        pointwise-node
          : (x : El (⅀ A' B-LHS))
          → transport (cong El LHS-path) x
          ≡ transport (cong El (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail)) x
        pointwise-node x =
            LHS-chain-node x
          ∙ σ-bridge-base (a-of-x x) (z-of-x x)
          ∙ sym (RHS-chain-on-pair (a-of-x x) (z-of-x x))
          ∙ cong (transport (cong El (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail)))
                 (retEq (⟦⅀⟧ A' B-LHS) x)

      -- Pointwise-equality packaged as `pathToEquiv`-equality.
      equivs-agree-node : pathToEquiv (cong El LHS-path)
                        ≡ pathToEquiv (cong El (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail))
      equivs-agree-node = equivEq (funExt pointwise-node)

      -- Code-level path identity: `LHS-path` and `cong (⅀ A') (funExt per-fibre-Δ)
      -- ∙ RHS-path-tail` coincide. Standard `InjSec` sandwich on `equivs-agree-node`.
      opaque
        bridge-node : LHS-path ≡ cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail
        bridge-node =
            sym (InjSec 𝒰 LHS-path)
          ∙ cong Inj equivs-agree-node
          ∙ InjSec 𝒰 (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail)

      -- The final assembly. Six steps:
      --   (1) Split LHS's `transport along LHS-path`: `substComposite` + `bridge-node`.
      --   (2) Re-`substComposite` along the RHS-side path components.
      --   (3) Use `fromPathP node-path-pre-assoc` to discharge the `cong (⅀ A')
      --       (funExt per-fibre-Δ)` leg, replacing `inner-LHS-node` with the
      --       substed `inner-RHS-node`-shape.
      --   (4) Re-`substComposite` to split `RHS-path-tail`.
      --   (5) `sym graft-subst-fst` to push the outer `subst` *into* the RHS
      --       `graft`, reconstructing the actual RHS.
      eq-node : LHS ≡ RHS
      eq-node =
          sym (substComposite (FreeOps K)
                              (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a)))
                              (Inj (⅀Assoc≃ (⅀ A' B') B C))
                              inner-LHS-node)
        ∙ cong (λ p → subst (FreeOps K) p inner-LHS-node) bridge-node
        ∙ substComposite (FreeOps K)
                         (cong (⅀ A') (funExt per-fibre-Δ))
                         RHS-path-tail
                         inner-LHS-node
        ∙ cong (subst (FreeOps K) RHS-path-tail) (fromPathP node-path-pre-assoc)
        ∙ substComposite (FreeOps K)
                         (⅀AssocD 𝒰 A' B'' C1)
                         (⅀-subst-path (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C))
                         inner-RHS-node
        ∙ sym (graft-subst-fst K (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C)
                                  (node A' (λ a' → ⅀ (B' a') (λ b' → B (paired a' b'))) k
                                        (λ a' → graft K (B' a') (λ b' → B (paired a' b'))
                                                      (ts' a') (λ b' → ts (paired a' b'))))
                                  (λ ab → tss (fst (equivFun (⟦⅀⟧ (⅀ A' B') B) ab))
                                              (snd (equivFun (⟦⅀⟧ (⅀ A' B') B) ab))))
  -- Set case: the `PathP` into the set `FreeOps K (⅀ (⅀ A B) (⅀Assoc-C' A B C))`
  -- is a proposition (`isOfHLevelPathP' 1`), so the square at the four faces of
  -- the input `set`-cell is filled by `isProp→SquareP` from four recursive
  -- `graft-assoc K A B C` calls.
  graft-assoc K A B C (set _ x y p q i j) ts tss =
    isProp→SquareP
      {B = λ i' j' → PathP (λ i'' → FreeOps K (Inj (⅀Assoc≃ A B C) i''))
                           (graft K A (λ a → ⅀ (B a) (C a)) (set A x y p q i' j')
                                  (λ a → graft K (B a) (C a) (ts a) (tss a)))
                           (graft K (⅀ A B) (⅀Assoc-C' A B C)
                                  (graft K A B (set A x y p q i' j') ts)
                                  (λ ab → tss (fst (equivFun (⟦⅀⟧ A B) ab))
                                              (snd (equivFun (⟦⅀⟧ A B) ab))))}
      (λ _ _ → isOfHLevelPathP' 1 (set _) _ _)
      (λ _ → graft-assoc K A B C x ts tss)
      (λ _ → graft-assoc K A B C y ts tss)
      (λ kk → graft-assoc K A B C (p kk) ts tss)
      (λ kk → graft-assoc K A B C (q kk) ts tss)
      i j

  -- ============================================================================
  -- §9  Operad assembly
  --
  -- The free 𝒰-operad on K, assembled from `leaf`, `graft`, and the three laws.
  -- ============================================================================
  FreeOperad : (K : Code → Type ℓk) → Operad 𝒰 (FreeOps K)
  Operad.isSetK (FreeOperad K) = set
  Operad.id     (FreeOperad K) = leaf
  Operad.compₒ  (FreeOperad K) = graft K
  Operad.idl    (FreeOperad K) = graft-idl K
  Operad.idr    (FreeOperad K) = graft-idr K
  Operad.assoc  (FreeOperad K) = graft-assoc K
