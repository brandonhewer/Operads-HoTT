{-# OPTIONS --cubical #-}
-- The free 𝒰-operad on a family K, presented as a higher inductive family.
-- Following FreeOperad.tex (lines 87-118): a HIT with leaf/node/set constructors.
--
-- Path-valued helpers (`funExt-q-decomp`, `snd-PathP`, `σ-bridge`, `LHS-chain`,
-- `RHS-chain`, `pointwise`, `bridge` for eq-leaf; `transp-⅀AB-factored`,
-- `transp-C'-eq-on-canonical`, `⟦⅀⟧-on-transp`, `snd-adjust-a'`,
-- `path-bridge-LHS-to-RHS`, … for eq-node) are wrapped in `opaque` to keep
-- cubical reductions sealed.  Never wrap an `isoToEquiv`- or equivalence-valued
-- definition in opaque — its `.equiv-proof` projection is load-bearing.
module HoTTOperads.Free.HIT where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (homotopyNatural)
open import Cubical.Foundations.HLevels using (isOfHLevelPathP')
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Foundations.GroupoidLaws using (lCancel ; rUnit ; lUnit ; assoc ; congFunct ; symDistr)
open import Cubical.Foundations.Path using (isProp→SquareP)
open import Cubical.Foundations.Univalence using (ua ; uaβ ; uaInvEquiv ; pathToEquiv ; pathToEquivRefl ; ua-pathToEquiv ; pathToEquiv-ua ; uaCompEquiv ; EquivJ)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; ΣPathP)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-snd)
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

  data FreeOps (K : Code → Type ℓk) : Code → Type (ℓ-max (ℓ-max ℓc ℓe) ℓk) where
    leaf : FreeOps K 𝜏
    node : (A : Code) (B : El A → Code)
         → K A → ((a : El A) → FreeOps K (B a))
         → FreeOps K (⅀ A B)
    set  : (A : Code) (x y : FreeOps K A) (p q : x ≡ y) → p ≡ q

  opaque
    -- Transport a node along a cong-of-⅀A-path: distributes over the index.
    -- By J on q. At q = refl, both sides reduce to `node A B₁ k ts` via substRefl.
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

  -- Cubical index path: ⅀ A (C ∘ transport p) ≡ ⅀ A' C. At i = 1 the inner
  -- transp is along a constant line starting from i1, hence the identity, so
  -- the path lands at ⅀ A' C definitionally.
  ⅀-subst-path : {A A' : Code} (p : A ≡ A') (C : El A' → Code)
               → ⅀ A (λ a → C (transport (cong El p) a)) ≡ ⅀ A' C
  ⅀-subst-path p C i = ⅀ (p i) (λ a → C (transp (λ j → El (p (i ∨ j))) i a))

  -- Push a subst across the outer graft. Built as fromPathP of a direct cubical
  -- filler: at each i, graft is applied to the partial-transport of t (so that
  -- the first FreeOps argument lives in FreeOps K (p i)) with the per-fibre
  -- function f reparameterised along the corresponding partial El-transport.
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

  -- Push subst-along-cong-⅀A across the outer graft into the per-fibre function.
  -- The codomain family rebases from C to C' via q, with the per-fibre function f
  -- substituted along funExt⁻ q a in the result.
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

  -- Transport along ⅀IdlD 𝒰 D coincides with the canonical inverse-Σ pre-image.
  -- Proven by decomposing the ⅀IdlD path into its two factors and applying ⟦⅀Idl⟧
  -- (relating ua of ⅀Idl≃ to cong El of Inj) and ⟦⅀⟧-natural-snd (computing the
  -- transport along the second-argument cong via Σ-cong-equiv-snd).
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

      -- transport along the inverse of ⅀Idl≃ is invEq applied via invEq-⅀Idl.
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

      -- transport along cong (⅀ 𝜏) const-X-D factors via ⟦⅀⟧-natural-snd. At the
      -- α-fibre, the per-fibre transport reduces to the identity because El 𝜏 is
      -- a prop, hence retEq ⟦𝜏⟧ α ≡ refl, hence funExt⁻ const-X-D α ≡ refl.
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

  -- Transport along ⅀-subst-path computes via the canonical Σ-rebase: send
  -- (a, c) under ⟦⅀⟧ to (transport (cong El p) a, c) and back via invEq ⟦⅀⟧.
  -- Provable by J on p: at p = refl, ⅀-subst-path refl C reduces (definitionally)
  -- to cong (⅀ A) (B-path) where B-path varies the second arg via transp on a
  -- constant family; the equation then follows from ⟦⅀⟧-natural-snd plus a
  -- ΣPathP rewrite swapping the per-fibre transport (Σ-snd form) for the first-
  -- component transport-refl form (Σ-fst form).
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

  -- Step-0 sanity probe: ⅀Assoc-C' A B C unfolds definitionally to the η-form on Σ.
  -- Used by eq-leaf's funExt-q-decomp.
  private
    Assoc-C'-uncurry-refl : (A : Code) (B : El A → Code) (C : (a : El A) → El (B a) → Code)
                          → ⅀Assoc-C' A B C
                          ≡ (λ ab → C (fst (equivFun (⟦⅀⟧ A B) ab))
                                       (snd (equivFun (⟦⅀⟧ A B) ab)))
    Assoc-C'-uncurry-refl _ _ _ = refl

  -- Left identity of graft: grafting at a leaf produces the right-hand subtree,
  -- modulo the canonical path ⅀ 𝜏 (λ _ → A) ≡ A.
  --
  -- For the constant codomain X = λ _ → A, the helper ⅀IdlD 𝒰 X used inside
  -- `graft K 𝜏 (λ _ → A) leaf (λ _ → t)` reduces definitionally to
  -- `sym (Inj (⅀Idl≃ A)) ∙ refl`, so composing with `Inj (⅀Idl≃ A)` cancels.
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

  -- Right identity of graft: grafting with leaves at every input is identity,
  -- modulo the canonical path ⅀ A (λ _ → 𝜏) ≡ A.
  graft-idr : (K : Code → Type ℓk) (A : Code) (t : FreeOps K A)
            → PathP (λ i → FreeOps K (Inj (⅀Idr≃ A) i))
                    (graft K A (λ _ → 𝜏) t (λ _ → leaf)) t
  -- Leaf case (A = 𝜏): both ⅀Idl≃ 𝜏 and ⅀Idr≃ 𝜏 are equivalences between
  -- propositional types, hence propositionally equal. The loop they form
  -- in Code reduces to refl.
  graft-idr K _ leaf = toPathP eq
    where
      opaque
        idl≡idr : ⅀Idl≃ 𝜏 ≡ ⅀Idr≃ 𝜏
        idl≡idr = propEquivEq (isPropEl-⅀𝜏𝜏 𝒰) (isPropEl𝜏 𝒰) (⅀Idl≃ 𝜏) (⅀Idr≃ 𝜏)

        loop-cancels : sym (Inj (⅀Idl≃ 𝜏)) ∙ Inj (⅀Idr≃ 𝜏) ≡ refl
        loop-cancels = cong (λ e → sym (Inj (⅀Idl≃ 𝜏)) ∙ Inj e) (sym idl≡idr)
                     ∙ lCancel (Inj (⅀Idl≃ 𝜏))

        reduce : ⅀IdlD 𝒰 (λ _ → 𝜏) ∙ Inj (⅀Idr≃ 𝜏) ≡ refl
        reduce = cong (_∙ Inj (⅀Idr≃ 𝜏)) (sym (rUnit (sym (Inj (⅀Idl≃ 𝜏)))))
               ∙ loop-cancels

        eq : transport (λ i → FreeOps K (Inj (⅀Idr≃ 𝜏) i))
                       (graft K 𝜏 (λ _ → 𝜏) leaf (λ _ → leaf)) ≡ leaf
        eq = sym (substComposite (FreeOps K) (⅀IdlD 𝒰 (λ _ → 𝜏)) (Inj (⅀Idr≃ 𝜏)) leaf)
           ∙ cong (λ p → subst (FreeOps K) p leaf) reduce
           ∙ substRefl {B = FreeOps K} leaf
  -- Node case: combines the IH per fibre with a structural cong-of-node path,
  -- then transfers across Code via the InjSec-driven bridge.
  graft-idr K _ (node A B k ts) = toPathP eq
    where
      -- Per-fibre path: Inj (⅀Idr≃ (B a)) : ⅀ (B a) (λ _ → 𝜏) ≡ B a.
      p : (a : El A) → ⅀ (B a) (λ _ → 𝜏) ≡ B a
      p a = Inj (⅀Idr≃ (B a))

      -- The intermediate node value before subst-by-⅀AssocD.
      inner-node : FreeOps K (⅀ A (λ a → ⅀ (B a) (λ _ → 𝜏)))
      inner-node = node A (λ a → ⅀ (B a) (λ _ → 𝜏)) k
                        (λ a → graft K (B a) (λ _ → 𝜏) (ts a) (λ _ → leaf))

      -- node-path: a structural PathP built by varying the B-arg and ts-arg of
      -- node along i, using the per-fibre IH.
      node-path : PathP (λ i → FreeOps K (⅀ A (λ a → p a i)))
                        inner-node (node A B k ts)
      node-path i = node A (λ a → p a i) k (λ a → graft-idr K (B a) (ts a) i)

      opaque
        -- Bridge: the two Code-level paths agree. Reduce via InjSec to El-level
        -- equivalence equality, then unify both sides via Σ-decomposition.
        bridge : ⅀AssocD 𝒰 A B (λ _ → 𝜏) ∙ Inj (⅀Idr≃ (⅀ A B))
               ≡ cong (⅀ A) (funExt p)
        bridge =
            sym (InjSec 𝒰 (⅀AssocD 𝒰 A B (λ _ → 𝜏) ∙ Inj (⅀Idr≃ (⅀ A B))))
          ∙ cong Inj equivs-agree
          ∙ InjSec 𝒰 (cong (⅀ A) (funExt p))
          where
            -- LHS-of-bridge cong-El simplification → compEquiv ⅀Assoc≃ ⅀Idr≃.
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

            -- RHS-of-bridge cong-El simplification → Σ-cong-equiv-snd form via ⟦⅀⟧-naturality.
            -- For p a = Inj (⅀Idr≃ (B a)): pathToEquiv (cong El (p a)) = ⅀Idr≃ (B a).
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

            -- Combine: LHS-equiv ≡ RHS-equiv. Use that compEquiv ⅀Assoc≃ ⅀Idr≃ equals
            -- the Σ-cong-equiv-snd composite, by equivEq + funExt.
            -- Both compEquiv ⅀Assoc≃ ⅀Idr≃ and the Σ-cong-equiv-snd composite send
            -- x ↦ invEq (⟦⅀⟧ A B) (a, b) where (a, σ) = ⟦⅀⟧ x and (b, _) = ⟦⅀⟧ σ.
            -- The only non-definitional step is the secEq invocation cancelling
            -- the inner `equivFun ⟦⅀⟧ ∘ invEq ⟦⅀⟧` on the LHS chain.
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
  -- Set case: the goal type is a PathP into the set FreeOps K A, hence a
  -- proposition. Fill the resulting square via isProp→SquareP.
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

  -- Associativity of graft. Induction on t. Both leaf and node cases reduce
  -- (after toPathP) to a set-level path between substed-graft expressions;
  -- in each, a Code-level bridge plays the same role as in graft-idr.
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
  -- Leaf case (A = 𝜏): the LHS reduces via graft's leaf clause to a subst
  -- applied to graft K (B α) (C α) (ts α) (tss α). The RHS contains
  -- graft K (⅀ 𝜏 B) ... (subst (⅀IdlD 𝒰 B) (ts α)) (...), where the third
  -- argument is opaque (subst-of-arbitrary-FreeOps doesn't reduce on HIT
  -- constructors). Discharging this constructively requires a nested
  -- induction on `ts α` to compute the RHS graft for each constructor case,
  -- mirroring the toPathP + InjSec + ⟦⅀⟧-natural-snd + Σ-decomp recipe used
  -- in graft-idr's node case.
  graft-assoc K _ B C leaf ts tss = toPathP eq-leaf
    where
      α : El 𝜏
      α = invEq ⟦𝜏⟧ tt

      D₀ : El 𝜏 → Code
      D₀ a = ⅀ (B a) (C a)

      transp-B : El (B α) → El (⅀ 𝜏 B)
      transp-B = transport (cong El (⅀IdlD 𝒰 B))

      pair-eq : (b : El (B α)) → equivFun (⟦⅀⟧ 𝜏 B) (transp-B b) ≡ (α , b)
      pair-eq b = cong (equivFun (⟦⅀⟧ 𝜏 B)) (transp-⅀IdlD B b)
                ∙ secEq (⟦⅀⟧ 𝜏 B) (α , b)

      pair-path : (b : El (B α)) → (α , b) ≡ equivFun (⟦⅀⟧ 𝜏 B) (transp-B b)
      pair-path b = sym (pair-eq b)

      C-uncurry : Σ (El 𝜏) (λ a → El (B a)) → Code
      C-uncurry (a , b) = C a b

      tss-uncurry : (p : Σ (El 𝜏) (λ a → El (B a))) → FreeOps K (C-uncurry p)
      tss-uncurry (a , b) = tss a b

      C' : El (B α) → Code
      C' b = ⅀Assoc-C' 𝜏 B C (transp-B b)

      f' : (b : El (B α)) → FreeOps K (C' b)
      f' b = tss (fst (equivFun (⟦⅀⟧ 𝜏 B) (transp-B b)))
                 (snd (equivFun (⟦⅀⟧ 𝜏 B) (transp-B b)))

      q-fn : (b : El (B α)) → C α b ≡ C' b
      q-fn b = cong C-uncurry (pair-path b)

      q : C α ≡ C'
      q = funExt q-fn

      tss-eq-fn : (b : El (B α)) → subst (FreeOps K) (funExt⁻ q b) (tss α b) ≡ f' b
      tss-eq-fn b = fromPathP {A = λ i → FreeOps K (q-fn b i)}
                              (cong tss-uncurry (pair-path b))

      tss-eq : (λ b → subst (FreeOps K) (funExt⁻ q b) (tss α b)) ≡ f'
      tss-eq = funExt tss-eq-fn

      inner-graft : FreeOps K (⅀ (B α) (C α))
      inner-graft = graft K (B α) (C α) (ts α) (tss α)

      LHS RHS : FreeOps K (Inj (⅀Assoc≃ 𝜏 B C) i1)
      LHS = transport (λ i → FreeOps K (Inj (⅀Assoc≃ 𝜏 B C) i))
                      (graft K 𝜏 (λ a → ⅀ (B a) (C a)) leaf
                             (λ a → graft K (B a) (C a) (ts a) (tss a)))
      RHS = graft K (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)
                  (graft K 𝜏 B leaf ts)
                  (λ ab → tss (fst (equivFun (⟦⅀⟧ 𝜏 B) ab))
                              (snd (equivFun (⟦⅀⟧ 𝜏 B) ab)))

      -- eq-leaf : LHS ≡ RHS — fully constructive.
      -- Strategy: Code-level `bridge` via InjSec + pointwise descent through
      -- `⅀Assoc≃` (one secEq + subst-of-Σ-snd), then chain with substComposite,
      -- graft-subst-snd, tss-eq, sym graft-subst-fst.
      -- Helpers built below: funExt-q-decomp, c₀'-of, snd-PathP, σ-bridge,
      -- ⅀Assoc-cont, LHS-chain, RHS-chain, pointwise, equivs-agree, bridge.

      -- funExt-q-decomp: split funExt⁻ q b₀ into the two factors used to
      -- characterise the snd-PathP. Uses symDistr + congFunct; the final
      -- step `cong C-uncurry ∘ cong (equivFun ⟦⅀⟧) = cong (⅀Assoc-C' …)` is
      -- definitional via Assoc-C'-uncurry-refl.
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

      -- c₀'-of x : the "shifted" snd component of the LHS-of-bridge transport.
      -- Definitionally equal to `subst (λ ab → El (C (fst ab) (snd ab))) (sym (secEq …)) c₀`
      -- which arises from unfolding invEq (Σ-cong-equiv-fst (⟦⅀⟧ 𝜏 B)).
      c₀'-of : (x : El (⅀ (B α) (C α))) → El (⅀Assoc-C' 𝜏 B C (invEq (⟦⅀⟧ 𝜏 B)
                                                              (α , fst (equivFun (⟦⅀⟧ (B α) (C α)) x))))
      c₀'-of x = subst (λ ab → El (C (fst ab) (snd ab)))
                       (sym (secEq (⟦⅀⟧ 𝜏 B)
                                   (α , fst (equivFun (⟦⅀⟧ (B α) (C α)) x))))
                       (snd (equivFun (⟦⅀⟧ (B α) (C α)) x))

      -- snd-PathP: heterogeneous path bridging the two snd-components of σ-bridge.
      -- Built as transport-filler glued via funExt-q-decomp.
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

      -- σ-bridge: the Σ-pair bridge inside `invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))`.
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

      -- ⅀Assoc-cont: the "continuation" of ⅀Assoc≃ 𝜏 B C after equivFun (⟦⅀⟧ 𝜏 D₀).
      -- By compEquiv reduction, `equivFun (⅀Assoc≃ 𝜏 B C) y ≡ ⅀Assoc-cont (equivFun (⟦⅀⟧ 𝜏 D₀) y)`
      -- definitionally. We name it so we can rewrite under it via cong (⅀Assoc-cont) (secEq …).
      open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-fst ; Σ-assoc-≃)

      ⅀Assoc-cont : Σ (El 𝜏) (λ a → El (D₀ a)) → El (⅀ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))
      ⅀Assoc-cont p =
        invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))
              (invEq (Σ-cong-equiv-fst {B = λ ab → El (C (fst ab) (snd ab))} (⟦⅀⟧ 𝜏 B))
                     (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B a) (C a))) p)))

      -- Sanity probe: ⅀Assoc-cont is the strict continuation of ⅀Assoc≃ post-⟦⅀⟧.
      ⅀Assoc-cont-refl : (y : El (⅀ 𝜏 D₀))
                       → equivFun (⅀Assoc≃ 𝜏 B C) y ≡ ⅀Assoc-cont (equivFun (⟦⅀⟧ 𝜏 D₀) y)
      ⅀Assoc-cont-refl _ = refl

      -- Sanity probe: ⅀Assoc-cont applied to (α , x) gives the explicit invEq form.
      -- This is what the LHS-chain's final form unfolds to definitionally.
      ⅀Assoc-cont-at-αx : (x : El (⅀ (B α) (C α)))
                        → ⅀Assoc-cont (α , x)
                        ≡ invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))
                                (invEq (⟦⅀⟧ 𝜏 B) (α , fst (equivFun (⟦⅀⟧ (B α) (C α)) x))
                                , c₀'-of x)
      ⅀Assoc-cont-at-αx _ = refl

      -- LHS-chain: reduces transport along ⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ …) to its canonical
      -- invEq-of-Σ-pair form. The only propositional step is secEq (⟦⅀⟧ 𝜏 D₀) (α , x); the
      -- rest is congFunct/substComposite for the path-composition and ⟦⅀Assoc⟧ + uaβ to
      -- convert the transport along Inj (⅀Assoc≃) into equivFun (⅀Assoc≃).
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
          ∙ cong (λ p → transport p (invEq (⟦⅀⟧ 𝜏 D₀) (α , x)))
                 (sym (⟦⅀Assoc⟧ 𝜏 B C))
          ∙ uaβ (⅀Assoc≃ 𝜏 B C) (invEq (⟦⅀⟧ 𝜏 D₀) (α , x))
          ∙ cong ⅀Assoc-cont (secEq (⟦⅀⟧ 𝜏 D₀) (α , x))

      -- RHS-chain: reduces transport along cong (⅀ (B α)) q ∙ ⅀-subst-path … to its
      -- canonical form. The only propositional step is secEq (⟦⅀⟧ (B α) C') (b₀, …).
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
            -- transport-q-x: transport along cong (⅀ (B α)) q rewrites to invEq-of-pair.
            transport-q-x : transport (cong El (cong (⅀ (B α)) q)) x
                          ≡ invEq (⟦⅀⟧ (B α) C') (b₀-of x , c₀-transported x)
            transport-q-x =
                cong (λ e → equivFun e x) (⟦⅀⟧-natural-snd 𝒰 (B α) q)

      -- pointwise: the heart of the bridge proof — equates the two transports at every x.
      opaque
        pointwise : (x : El (⅀ (B α) (C α)))
                  → transport (cong El (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C))) x
                  ≡ transport (cong El (cong (⅀ (B α)) q
                                        ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))) x
        pointwise x =
            LHS-chain x
          ∙ cong (invEq (⟦⅀⟧ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))) (σ-bridge x)
          ∙ sym (RHS-chain x)

      -- equivs-agree: pointwise wrapped as an equivalence equality.
      -- NOT opaque (equivalence-valued).
      equivs-agree : pathToEquiv (cong El (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C)))
                   ≡ pathToEquiv (cong El (cong (⅀ (B α)) q
                                        ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C)))
      equivs-agree = equivEq (funExt pointwise)

      -- bridge: the Code-level path identity used to convert LHS double-subst into
      -- the RHS form before applying graft-subst-{fst,snd} pushdowns.
      opaque
        bridge : ⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C)
               ≡ cong (⅀ (B α)) q ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C)
        bridge =
            sym (InjSec 𝒰 (⅀IdlD 𝒰 D₀ ∙ Inj (⅀Assoc≃ 𝜏 B C)))
          ∙ cong Inj equivs-agree
          ∙ InjSec 𝒰 (cong (⅀ (B α)) q ∙ ⅀-subst-path (⅀IdlD 𝒰 B) (⅀Assoc-C' 𝜏 B C))

      -- eq-leaf: the final chain.
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
  -- eq-node (graft-assoc on `node A' B' k ts'`).  The per-fibre IH
  -- `graft-assoc K (B' a') …` is supplied recursively for each a' : El A' and
  -- lifted into a `node-path-pre-assoc` via `cong (⅀ A') (funExt per-fibre-Δ)`.
  -- The Code-level `bridge-node` then aligns the LHS and RHS index paths,
  -- after which a 6-step `substComposite` chain assembles `eq-node` at the
  -- bottom of this `where` block.
  graft-assoc K _ B C (node A' B' k ts') ts tss = toPathP eq-node
    where
      open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-fst ; Σ-assoc-≃)

      -- Canonical "pairing": the inverse of ⟦⅀⟧ A' B'.
      paired : (a' : El A') → El (B' a') → El (⅀ A' B')
      paired a' b' = invEq (⟦⅀⟧ A' B') (a' , b')

      -- The intermediate index family after pushing graft-subst-fst.
      B'' : El A' → Code
      B'' a' = ⅀ (B' a') (λ b' → B (paired a' b'))

      -- transport along ⅀AssocD 𝒰 A' B' B : ⅀ A' B'' ≡ ⅀ (⅀ A' B') B.
      transp-⅀AB : El (⅀ A' B'') → El (⅀ (⅀ A' B') B)
      transp-⅀AB = transport (cong El (⅀AssocD 𝒰 A' B' B))

      -- The post-⅀AssocD codomain on B'' : C1 z = ⅀Assoc-C' (⅀ A' B') B C (transp-⅀AB z).
      C1 : El (⅀ A' B'') → Code
      C1 z = ⅀Assoc-C' (⅀ A' B') B C (transp-⅀AB z)

      -- "C-uncurry" at the top Σ-level: a helper for cong-of-cong calculations.
      C-curry-top : Σ (El (⅀ A' B')) (λ ab → El (B ab)) → Code
      C-curry-top (ab , b'') = C ab b''

      tss-curry-top : (p : Σ (El (⅀ A' B')) (λ ab → El (B ab))) → FreeOps K (C-curry-top p)
      tss-curry-top (ab , b'') = tss ab b''

      LHS RHS : FreeOps K (Inj (⅀Assoc≃ (⅀ A' B') B C) i1)
      LHS = transport (λ i → FreeOps K (Inj (⅀Assoc≃ (⅀ A' B') B C) i))
                      (graft K (⅀ A' B') (λ a → ⅀ (B a) (C a)) (node A' B' k ts')
                             (λ a → graft K (B a) (C a) (ts a) (tss a)))
      RHS = graft K (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
                  (graft K (⅀ A' B') B (node A' B' k ts') ts)
                  (λ ab → tss (fst (equivFun (⟦⅀⟧ (⅀ A' B') B) ab))
                              (snd (equivFun (⟦⅀⟧ (⅀ A' B') B) ab)))

      -- The inner subst-of-node on the LHS, before the outer Inj-transport.
      B-LHS : El A' → Code
      B-LHS a' = ⅀ (B' a') (λ b' → ⅀ (B (paired a' b')) (C (paired a' b')))

      inner-LHS-node : FreeOps K (⅀ A' B-LHS)
      inner-LHS-node = node A' B-LHS k
                            (λ a' → graft K (B' a')
                                          (λ b' → ⅀ (B (paired a' b')) (C (paired a' b')))
                                          (ts' a')
                                          (λ b' → graft K (B (paired a' b')) (C (paired a' b'))
                                                        (ts (paired a' b')) (tss (paired a' b'))))

      -- The inner-RHS-actual-node after pushing graft-subst-fst + reducing graft on node.
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

      -- (a) The Σ-level rebase for transp-⅀AB at canonical points.  Characterises
      -- the iterated `equivFun ⟦⅀⟧ ∘ transp-⅀AB ∘ invEq ⟦⅀⟧` combinator on (a', z)
      -- inputs — the `transp-⅀AssocD` analog of `transp-⅀IdlD`.
      module _ (a' : El A') (z : El (B'' a')) where
        b'-of : El (B' a')
        b'-of = fst (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) z)
        c'-of : El (B (paired a' b'-of))
        c'-of = snd (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) z)

      -- The "intermediate" family used in ⅀AssocD's decomposition:
      C-int : (a : El A') → El (B' a) → Code
      C-int a b = B (paired a b)

      -- C'-eq : ⅀Assoc-C' A' B' C-int ≡ B, exactly as in the body of ⅀AssocD.
      C'-eq : ⅀Assoc-C' A' B' C-int ≡ B
      C'-eq = funExt (λ x → cong B (retEq (⟦⅀⟧ A' B') x))

      -- Step (a-1): transp via ⅀Assoc 𝒰 A' B' C-int factor.
      -- Use ⟦⅀Assoc⟧ + uaβ. This is the same incantation as eq-leaf's LHS-chain step.
      opaque
        step-Assoc-on-pair : (a' : El A') (z : El (B'' a'))
                           → transport (cong El (Inj (⅀Assoc≃ A' B' C-int)))
                                       (invEq (⟦⅀⟧ A' B'') (a' , z))
                           ≡ equivFun (⅀Assoc≃ A' B' C-int)
                                      (invEq (⟦⅀⟧ A' B'') (a' , z))
        step-Assoc-on-pair a' z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B'') (a' , z)))
                 (sym (⟦⅀Assoc⟧ A' B' C-int))
          ∙ uaβ (⅀Assoc≃ A' B' C-int) (invEq (⟦⅀⟧ A' B'') (a' , z))

      -- Step (a-2): equivFun ⅀Assoc≃ unfolds at canonical input via secEq.
      -- ⅀Assoc≃ A' B' C-int = ⟦⅀⟧ A' B''-int ⨟ Σ-cong-equiv-snd (⟦⅀⟧ (B' a) (C-int a))
      --                       ⨟ invEquiv Σ-assoc-≃ ⨟ invEquiv (Σ-cong-equiv-fst (⟦⅀⟧ A' B'))
      --                       ⨟ invEquiv (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
      -- where B''-int a = ⅀ (B' a) (C-int a) = B'' a definitionally.
      -- Apply to invEq (⟦⅀⟧ A' B'') (a' , z):
      --   step 1: equivFun (⟦⅀⟧ A' B'') (invEq … (a' , z)) = (a' , z) via secEq.
      --   step 2-4: η-Σ unfolding (definitional) reduces to:
      --     invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int)) (paired a' b'-of , c'-substed)
      --   where c'-substed = subst (λ p → El (C-int (fst p) (snd p))) (sym (secEq ⟦⅀⟧A'B' (paired a' b'-of))) c'-of.
      Assoc-cont : (a' : El A') (z : El (B'' a'))
                 → El (⅀ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
      Assoc-cont a' z =
        invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
              (invEq (Σ-cong-equiv-fst {B = λ ab → El (C-int (fst ab) (snd ab))} (⟦⅀⟧ A' B'))
                     (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B' a) (C-int a)))
                                      (a' , z))))

      opaque
        Assoc-cont-refl : (a' : El A') (z : El (B'' a'))
                        → equivFun (⅀Assoc≃ A' B' C-int) (invEq (⟦⅀⟧ A' B'') (a' , z))
                        ≡ Assoc-cont a' z
        Assoc-cont-refl a' z =
          cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                            (invEq (Σ-cong-equiv-fst {B = λ ab → El (C-int (fst ab) (snd ab))} (⟦⅀⟧ A' B'))
                                   (invEq Σ-assoc-≃
                                          (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B' a) (C-int a))) p))))
               (secEq (⟦⅀⟧ A' B'') (a' , z))

      -- The transport along cong (⅀ (⅀ A' B')) C'-eq is via ⟦⅀⟧-natural-snd.
      -- This produces a Σ-pair on the (⅀ A' B', B)-side via the canonical secEq cancellation.

      transp-C'-eq : El (⅀ (⅀ A' B') (⅀Assoc-C' A' B' C-int)) → El (⅀ (⅀ A' B') B)
      transp-C'-eq = transport (cong (λ B'' → El (⅀ (⅀ A' B') B'')) C'-eq)

      -- The full transp-⅀AB factors via the two segments.
      opaque
        transp-⅀AB-factored : (a' : El A') (z : El (B'' a'))
                            → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , z))
                            ≡ transp-C'-eq (Assoc-cont a' z)
        transp-⅀AB-factored a' z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B'') (a' , z)))
                 (congFunct El (Inj (⅀Assoc≃ A' B' C-int)) (cong (⅀ (⅀ A' B')) C'-eq))
          ∙ substComposite (λ X → X)
                           (cong El (Inj (⅀Assoc≃ A' B' C-int)))
                           (cong El (cong (⅀ (⅀ A' B')) C'-eq))
                           (invEq (⟦⅀⟧ A' B'') (a' , z))
          ∙ cong transp-C'-eq (step-Assoc-on-pair a' z ∙ Assoc-cont-refl a' z)

      -- substed-c-of: the canonical "shifted" c-component arising from
      -- invEq (Σ-cong-equiv-fst (⟦⅀⟧ A' B')) ((a', b'-of), c'-of). Used in
      -- Assoc-cont-explicit and downstream in snd-adjust-a'.
      substed-c-of : (a' : El A') (z : El (B'' a'))
                   → El (⅀Assoc-C' A' B' C-int (paired a' (b'-of a' z)))
      substed-c-of a' z =
        subst (λ ab → El (C-int (fst ab) (snd ab)))
              (sym (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z)))
              (c'-of a' z)

      -- Assoc-cont reduces (definitionally up to η-Σ) to the above.
      Assoc-cont-explicit : (a' : El A') (z : El (B'' a'))
                          → Assoc-cont a' z
                          ≡ invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C-int))
                                  (paired a' (b'-of a' z) , substed-c-of a' z)
      Assoc-cont-explicit _ _ = refl

      -- transp-C'-eq on this canonical pair, via ⟦⅀⟧-natural-snd + secEq.
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

      -- We need to apply equivFun (⟦⅀⟧ (⅀ A' B') B) to the RHS to extract the pair.
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
                 (transp-⅀AB-factored a' z ∙ cong transp-C'-eq (Assoc-cont-explicit a' z)
                                           ∙ transp-C'-eq-on-canonical a' z)
          ∙ secEq (⟦⅀⟧ (⅀ A' B') B) _

      -- adj-coh: the half-adjoint coherence of an equivalence. From EquivJ at idEquiv
      -- (where both sides are refl).
      opaque
        adj-coh : ∀ {ℓ} {A B' : Type ℓ} (e : A ≃ B') (b : B')
                → cong (invEq e) (secEq e b) ≡ retEq e (invEq e b)
        adj-coh {B' = B'} e =
          EquivJ (λ _ e' → (b : B') → cong (invEq e') (secEq e' b) ≡ retEq e' (invEq e' b))
                 (λ _ → refl) e

      -- key-eq: `cong El (funExt⁻ C'-eq (paired a' (b'-of))) ≡
      --          cong (λ ab → El (C-int (fst ab) (snd ab))) (secEq (⟦⅀⟧ A' B') (a' , b'-of))`.
      -- Follows from adj-coh applied to ⟦⅀⟧ A' B'.
      opaque
        key-eq : (a' : El A') (z : El (B'' a'))
               → cong El (funExt⁻ C'-eq (paired a' (b'-of a' z)))
               ≡ cong (λ ab → El (C-int (fst ab) (snd ab)))
                      (secEq (⟦⅀⟧ A' B') (a' , b'-of a' z))
        key-eq a' z = cong (cong (λ x → El (B x)))
                           (sym (adj-coh (⟦⅀⟧ A' B') (a' , b'-of a' z)))

      -- c'-of-eq: transporting substed-c-of along (cong El (funExt⁻ C'-eq …)) recovers c'-of.
      -- Uses key-eq to align the two cong-paths, then the composed path lCancels to refl.
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

      -- (b) snd-adjust-a' : the codomain functions on B'' a' are equal.
      -- LHS : ⅀Assoc-C' (B' a') (B ∘ paired a') (λ b' b'' → C (paired a' b') b'')
      --     = λ z → C (paired a' (fst (⟦⅀⟧ (B' a') ...) z)) (snd (⟦⅀⟧ ...) z)
      -- RHS : λ z → C1 (invEq (⟦⅀⟧ A' B'') (a' , z))
      --     = λ z → C-curry-top (equivFun ⟦⅀⟧ (...) (transp-⅀AB (invEq ⟦⅀⟧ ...)))
      -- Bridge: (paired, c'-of) ≡ (paired, transport ... substed-c-of) ≡ equivFun ⟦⅀⟧ (...).
      opaque
        snd-adjust-a' : (a' : El A')
                      → ⅀Assoc-C' (B' a') (λ b' → B (paired a' b')) (λ b' b'' → C (paired a' b') b'')
                      ≡ (λ z → C1 (invEq (⟦⅀⟧ A' B'') (a' , z)))
        snd-adjust-a' a' = funExt (λ z →
            cong C-curry-top (ΣPathP (refl , c'-of-eq a' z))
          ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a' z)))

      -- (c) The per-fibre PathP: combining the per-fibre IH with snd-adjust-a'.
      -- Per-fibre IH provides a PathP over `Inj (⅀Assoc≃ (B' a') (B ∘ paired a') (λ b' b'' → C ...))`.
      -- The RHS of this PathP has codomain `⅀Assoc-C' (B' a') ...`; we transport via
      -- `cong (⅀ (B'' a')) snd-adjust-a'` to land at `λ z → C1 (invEq (⟦⅀⟧ A' B'') (a' , z))`.

      per-fibre-IH-from : (a' : El A') → FreeOps K (B-LHS a')
      per-fibre-IH-from a' =
        graft K (B' a') (λ b' → ⅀ (B (paired a' b')) (C (paired a' b')))
              (ts' a')
              (λ b' → graft K (B (paired a' b')) (C (paired a' b'))
                            (ts (paired a' b')) (tss (paired a' b')))

      per-fibre-IH-to : (a' : El A')
                      → FreeOps K (⅀ (B'' a') (⅀Assoc-C' (B' a') (λ b' → B (paired a' b'))
                                                                  (λ b' b'' → C (paired a' b') b'')))
      per-fibre-IH-to a' =
        graft K (⅀ (B' a') (λ b' → B (paired a' b')))
              (⅀Assoc-C' (B' a') (λ b' → B (paired a' b')) (λ b' b'' → C (paired a' b') b''))
              (graft K (B' a') (λ b' → B (paired a' b')) (ts' a') (λ b' → ts (paired a' b')))
              (λ ab → tss (paired a' (fst (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) ab)))
                          (snd (equivFun (⟦⅀⟧ (B' a') (λ b' → B (paired a' b'))) ab)))

      per-fibre-IH-PathP : (a' : El A')
                        → PathP (λ i → FreeOps K (Inj (⅀Assoc≃ (B' a') (λ b' → B (paired a' b'))
                                                                (λ b' b'' → C (paired a' b') b'')) i))
                                (per-fibre-IH-from a') (per-fibre-IH-to a')
      per-fibre-IH-PathP a' =
        graft-assoc K (B' a') (λ b' → B (paired a' b'))
                    (λ b' b'' → C (paired a' b') b'')
                    (ts' a') (λ b' → ts (paired a' b')) (λ b' b'' → tss (paired a' b') b'')

      -- The per-fibre-Δ a' is the Code-path used inside `cong (⅀ A') (funExt …)` for bridge.
      per-fibre-Δ : (a' : El A') → B-LHS a' ≡ B-RHS a'
      per-fibre-Δ a' = Inj (⅀Assoc≃ (B' a') (λ b' → B (paired a' b')) (λ b' b'' → C (paired a' b') b''))
                     ∙ cong (⅀ (B'' a')) (snd-adjust-a' a')

      -- Continuation-adjustment: the per-fibre IH's "tss"-continuation, post substing,
      -- equals the actual RHS-side "tss-curry-top ∘ ⟦⅀⟧ ∘ transp-⅀AB ∘ invEq ⟦⅀⟧" form.
      -- This is the analog of tss-eq in eq-leaf.
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

      -- per-fibre-RHS-actual = ts-RHS a' from inner-RHS-node.
      per-fibre-RHS-actual : (a' : El A') → FreeOps K (B-RHS a')
      per-fibre-RHS-actual a' =
        graft K (B'' a') (λ b' → C1 (invEq (⟦⅀⟧ A' B'') (a' , b')))
              (graft K (B' a') (λ b' → B (paired a' b')) (ts' a') (λ b' → ts (paired a' b')))
              (λ b' → tss-curry-top (equivFun (⟦⅀⟧ (⅀ A' B') B)
                                              (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a' , b')))))

      -- per-fibre PathP: composes per-fibre IH with snd-adjust via graft-subst-snd.
      per-fibre-Δ-PathP : (a' : El A')
                       → PathP (λ i → FreeOps K (per-fibre-Δ a' i))
                               (per-fibre-IH-from a') (per-fibre-RHS-actual a')
      per-fibre-Δ-PathP a' = compPathP' {B = FreeOps K} (per-fibre-IH-PathP a') (toPathP step2)
        where
          -- step2 : subst (FreeOps K) (cong (⅀ (B'' a')) (snd-adjust-a' a')) (per-fibre-IH-to a')
          --       ≡ per-fibre-RHS-actual a'
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

      -- (d) node-path-pre-assoc: heterogeneous path from inner-LHS-node to inner-RHS-node.
      node-path-pre-assoc : PathP (λ i → FreeOps K (⅀ A' (λ a' → per-fibre-Δ a' i)))
                                  inner-LHS-node inner-RHS-node
      node-path-pre-assoc i = node A' (λ a' → per-fibre-Δ a' i) k
                                   (λ a' → per-fibre-Δ-PathP a' i)

      -- The "bridge" path in Code: equates the LHS-Code-side path with the RHS-Code-side path.
      LHS-path : ⅀ A' B-LHS ≡ ⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
      LHS-path = ⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a)) ∙ Inj (⅀Assoc≃ (⅀ A' B') B C)

      RHS-path-tail : ⅀ A' B-RHS ≡ ⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)
      RHS-path-tail = ⅀AssocD 𝒰 A' B'' C1
                    ∙ ⅀-subst-path (⅀AssocD 𝒰 A' B' B) (⅀Assoc-C' (⅀ A' B') B C)

      -- ================================================================
      -- bridge-node: constructive proof.
      -- ================================================================
      -- Strategy: sandwich the path equality between sym (InjSec) and InjSec,
      -- reducing it to equivalence-equality on cong El. The equivalence-equality
      -- is then proved pointwise (equivEq + funExt), and pointwise both sides
      -- reduce to a canonical 3-deep Σ-shuffle Σ-form.
      --
      -- The proof mirrors `bridge` in the leaf case (line 738) at the next
      -- Σ-level up. Helpers below are the node-case analogs of:
      --   - C-int / C'-eq (line 853-857)  →  C'-out / C'-eq-out (mid-level)
      --   - step-Assoc-on-pair (863)     →  step-Assoc-on-pair-LHS (mid-level)
      --                                    + step-Assoc-on-pair-outer (outermost)
      --   - Assoc-cont (883), Assoc-cont-refl (893)
      --       →  Assoc-cont-LHS + Assoc-cont-LHS-refl (mid-level)
      --       →  outer-Assoc-cont + outer-Assoc-cont-refl (outermost)
      --   - transp-⅀AB-factored (911)    →  transp-⅀AssocD-LHS-on-pair (mid)
      --                                    + transp-⅀AssocD-RHS-on-pair (RHS)
      --   - transp-C'-eq-on-canonical (942), ⟦⅀⟧-on-transp (962)
      --                                  →  variants for LHS and RHS chains
      --   - key-eq (987), c'-of-eq (997) →  key-eq-LHS, c'-of-eq-LHS
      --                                    (and corresponding RHS variants)

      -- ----- Mid-level family and equality -----
      C'-out : (a : El A') → El (B' a) → Code
      C'-out a b = ⅀ (B (paired a b)) (C (paired a b))

      C'-eq-out : ⅀Assoc-C' A' B' C'-out ≡ (λ a → ⅀ (B a) (C a))
      C'-eq-out = funExt (λ ab → cong (λ AB → ⅀ (B AB) (C AB)) (retEq (⟦⅀⟧ A' B') ab))

      -- Assoc-cont-LHS : canonical Σ-shuffle continuation for ⅀Assoc≃ A' B' C'-out.
      Assoc-cont-LHS : (a : El A') (z : El (B-LHS a))
                     → El (⅀ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
      Assoc-cont-LHS a z =
        invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
              (invEq (Σ-cong-equiv-fst {B = λ ab → El (C'-out (fst ab) (snd ab))} (⟦⅀⟧ A' B'))
                     (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B' a) (C'-out a))) (a , z))))

      opaque
        Assoc-cont-LHS-refl : (a : El A') (z : El (B-LHS a))
                            → equivFun (⅀Assoc≃ A' B' C'-out) (invEq (⟦⅀⟧ A' B-LHS) (a , z))
                            ≡ Assoc-cont-LHS a z
        Assoc-cont-LHS-refl a z =
          cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
                             (invEq (Σ-cong-equiv-fst {B = λ ab → El (C'-out (fst ab) (snd ab))} (⟦⅀⟧ A' B'))
                                    (invEq Σ-assoc-≃
                                           (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B' a) (C'-out a))) p))))
               (secEq (⟦⅀⟧ A' B-LHS) (a , z))

      opaque
        step-Assoc-on-pair-LHS : (a : El A') (z : El (B-LHS a))
                               → transport (cong El (Inj (⅀Assoc≃ A' B' C'-out)))
                                           (invEq (⟦⅀⟧ A' B-LHS) (a , z))
                               ≡ equivFun (⅀Assoc≃ A' B' C'-out) (invEq (⟦⅀⟧ A' B-LHS) (a , z))
        step-Assoc-on-pair-LHS a z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
                 (sym (⟦⅀Assoc⟧ A' B' C'-out))
          ∙ uaβ (⅀Assoc≃ A' B' C'-out) (invEq (⟦⅀⟧ A' B-LHS) (a , z))

      transp-C'-eq-out : El (⅀ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
                       → El (⅀ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
      transp-C'-eq-out = transport (cong (λ B'' → El (⅀ (⅀ A' B') B'')) C'-eq-out)

      -- Explicit "snd" components used in the LHS chain.
      b-of-LHS : (a : El A') (z : El (B-LHS a)) → El (B' a)
      b-of-LHS a z = fst (equivFun (⟦⅀⟧ (B' a) (C'-out a)) z)

      w-of-LHS : (a : El A') (z : El (B-LHS a)) → El (C'-out a (b-of-LHS a z))
      w-of-LHS a z = snd (equivFun (⟦⅀⟧ (B' a) (C'-out a)) z)

      substed-w-of-LHS : (a : El A') (z : El (B-LHS a))
                       → El (⅀Assoc-C' A' B' C'-out (paired a (b-of-LHS a z)))
      substed-w-of-LHS a z =
        subst (λ ab → El (C'-out (fst ab) (snd ab)))
              (sym (secEq (⟦⅀⟧ A' B') (a , b-of-LHS a z)))
              (w-of-LHS a z)

      Assoc-cont-LHS-explicit : (a : El A') (z : El (B-LHS a))
                              → Assoc-cont-LHS a z
                              ≡ invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
                                      (paired a (b-of-LHS a z) , substed-w-of-LHS a z)
      Assoc-cont-LHS-explicit _ _ = refl

      opaque
        transp-C'-eq-out-on-canonical
          : (a : El A') (z : El (B-LHS a))
          → transp-C'-eq-out (invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
                                     (paired a (b-of-LHS a z) , substed-w-of-LHS a z))
          ≡ invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
                  ( paired a (b-of-LHS a z)
                  , transport (cong El (funExt⁻ C'-eq-out (paired a (b-of-LHS a z))))
                              (substed-w-of-LHS a z))
        transp-C'-eq-out-on-canonical a z =
            cong (λ e → equivFun e (invEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
                                           (paired a (b-of-LHS a z) , substed-w-of-LHS a z)))
                 (⟦⅀⟧-natural-snd 𝒰 (⅀ A' B') C'-eq-out)
          ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
                              (fst p ,
                               transport (cong El (funExt⁻ C'-eq-out (fst p))) (snd p)))
                 (secEq (⟦⅀⟧ (⅀ A' B') (⅀Assoc-C' A' B' C'-out))
                        (paired a (b-of-LHS a z) , substed-w-of-LHS a z))

      opaque
        key-eq-LHS : (a : El A') (b : El (B' a))
                   → cong El (funExt⁻ C'-eq-out (paired a b))
                   ≡ cong (λ ab → El (C'-out (fst ab) (snd ab)))
                          (secEq (⟦⅀⟧ A' B') (a , b))
        key-eq-LHS a b = cong (cong (λ x → El (⅀ (B x) (C x))))
                              (sym (adj-coh (⟦⅀⟧ A' B') (a , b)))

      opaque
        c'-of-eq-LHS : (a : El A') (z : El (B-LHS a))
                     → w-of-LHS a z
                     ≡ transport (cong El (funExt⁻ C'-eq-out (paired a (b-of-LHS a z))))
                                 (substed-w-of-LHS a z)
        c'-of-eq-LHS a z =
            sym (transportRefl (w-of-LHS a z))
          ∙ cong (λ p → transport p (w-of-LHS a z))
                 (sym (lCancel (cong (λ ab → El (C'-out (fst ab) (snd ab)))
                                      (secEq (⟦⅀⟧ A' B') (a , b-of-LHS a z)))))
          ∙ cong (λ p → transport (cong (λ ab → El (C'-out (fst ab) (snd ab)))
                                         (sym (secEq (⟦⅀⟧ A' B') (a , b-of-LHS a z))) ∙ p)
                                    (w-of-LHS a z))
                 (sym (key-eq-LHS a (b-of-LHS a z)))
          ∙ substComposite (λ X → X)
                           (cong (λ ab → El (C'-out (fst ab) (snd ab)))
                                 (sym (secEq (⟦⅀⟧ A' B') (a , b-of-LHS a z))))
                           (cong El (funExt⁻ C'-eq-out (paired a (b-of-LHS a z))))
                           (w-of-LHS a z)

      -- transport-along-⅀AssocD on canonical pair: collapse the inner subst.
      opaque
        transp-⅀AssocD-LHS-on-pair
          : (a : El A') (z : El (B-LHS a))
          → transport (cong El (⅀AssocD 𝒰 A' B' (λ a → ⅀ (B a) (C a))))
                      (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ≡ invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
                  (paired a (b-of-LHS a z) , w-of-LHS a z)
        transp-⅀AssocD-LHS-on-pair a z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B-LHS) (a , z)))
                 (congFunct El (Inj (⅀Assoc≃ A' B' C'-out)) (cong (⅀ (⅀ A' B')) C'-eq-out))
          ∙ substComposite (λ X → X)
                           (cong El (Inj (⅀Assoc≃ A' B' C'-out)))
                           (cong El (cong (⅀ (⅀ A' B')) C'-eq-out))
                           (invEq (⟦⅀⟧ A' B-LHS) (a , z))
          ∙ cong transp-C'-eq-out (step-Assoc-on-pair-LHS a z ∙ Assoc-cont-LHS-refl a z)
          ∙ cong transp-C'-eq-out (Assoc-cont-LHS-explicit a z)
          ∙ transp-C'-eq-out-on-canonical a z
          ∙ cong (λ w → invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
                              (paired a (b-of-LHS a z) , w))
                 (sym (c'-of-eq-LHS a z))

      -- ----- Outer continuation: equivFun (⅀Assoc≃ (⅀ A' B') B C) on canonical pair -----
      outer-Assoc-cont : (ab : El (⅀ A' B')) (w : El (⅀ (B ab) (C ab)))
                      → El (⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
      outer-Assoc-cont ab w =
        invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
              (invEq (Σ-cong-equiv-fst {B = λ x → El (C (fst x) (snd x))} (⟦⅀⟧ (⅀ A' B') B))
                     (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd (λ x → ⟦⅀⟧ (B x) (C x))) (ab , w))))

      opaque
        outer-Assoc-cont-refl
          : (ab : El (⅀ A' B')) (w : El (⅀ (B ab) (C ab)))
          → equivFun (⅀Assoc≃ (⅀ A' B') B C)
                     (invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a))) (ab , w))
          ≡ outer-Assoc-cont ab w
        outer-Assoc-cont-refl ab w =
          cong (λ p → invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
                             (invEq (Σ-cong-equiv-fst {B = λ x → El (C (fst x) (snd x))} (⟦⅀⟧ (⅀ A' B') B))
                                    (invEq Σ-assoc-≃
                                           (equivFun (Σ-cong-equiv-snd (λ x → ⟦⅀⟧ (B x) (C x))) p))))
               (secEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a))) (ab , w))

      -- The canonical Σ-form both LHS and RHS chains reduce to.
      canonical-form : (a : El A') (z : El (B-LHS a))
                     → El (⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
      canonical-form a z =
        outer-Assoc-cont (paired a (b-of-LHS a z)) (w-of-LHS a z)

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
          ∙ cong (λ p → transport p (invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
                                            (paired a (b-of-LHS a z) , w-of-LHS a z)))
                 (sym (⟦⅀Assoc⟧ (⅀ A' B') B C))
          ∙ uaβ (⅀Assoc≃ (⅀ A' B') B C)
                (invEq (⟦⅀⟧ (⅀ A' B') (λ a → ⅀ (B a) (C a)))
                       (paired a (b-of-LHS a z) , w-of-LHS a z))
          ∙ outer-Assoc-cont-refl (paired a (b-of-LHS a z)) (w-of-LHS a z)

      -- Extend to arbitrary x via retEq.
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

      -- ===== RHS chain =====

      -- C1'-out and C1'-eq-out: intermediate family for ⅀AssocD A' B'' C1.
      C1'-out : (a : El A') → El (B'' a) → Code
      C1'-out a b = C1 (invEq (⟦⅀⟧ A' B'') (a , b))

      C1'-eq-out : ⅀Assoc-C' A' B'' C1'-out ≡ C1
      C1'-eq-out = funExt (λ x → cong C1 (retEq (⟦⅀⟧ A' B'') x))

      -- Assoc-cont-RHS : continuation of equivFun (⅀Assoc≃ A' B'' C1'-out).
      Assoc-cont-RHS : (a : El A') (z : El (B-RHS a))
                     → El (⅀ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
      Assoc-cont-RHS a z =
        invEq (⟦⅀⟧ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
              (invEq (Σ-cong-equiv-fst {B = λ p → El (C1'-out (fst p) (snd p))} (⟦⅀⟧ A' B''))
                     (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B'' a) (C1'-out a))) (a , z))))

      opaque
        Assoc-cont-RHS-refl : (a : El A') (z : El (B-RHS a))
                            → equivFun (⅀Assoc≃ A' B'' C1'-out)
                                       (invEq (⟦⅀⟧ A' B-RHS) (a , z))
                            ≡ Assoc-cont-RHS a z
        Assoc-cont-RHS-refl a z =
          cong (λ p → invEq (⟦⅀⟧ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
                             (invEq (Σ-cong-equiv-fst {B = λ p → El (C1'-out (fst p) (snd p))} (⟦⅀⟧ A' B''))
                                    (invEq Σ-assoc-≃
                                           (equivFun (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B'' a) (C1'-out a))) p))))
               (secEq (⟦⅀⟧ A' B-RHS) (a , z))

      opaque
        step-Assoc-on-pair-RHS : (a : El A') (z : El (B-RHS a))
                               → transport (cong El (Inj (⅀Assoc≃ A' B'' C1'-out)))
                                           (invEq (⟦⅀⟧ A' B-RHS) (a , z))
                               ≡ equivFun (⅀Assoc≃ A' B'' C1'-out) (invEq (⟦⅀⟧ A' B-RHS) (a , z))
        step-Assoc-on-pair-RHS a z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B-RHS) (a , z)))
                 (sym (⟦⅀Assoc⟧ A' B'' C1'-out))
          ∙ uaβ (⅀Assoc≃ A' B'' C1'-out) (invEq (⟦⅀⟧ A' B-RHS) (a , z))

      transp-C1'-eq-out : El (⅀ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
                        → El (⅀ (⅀ A' B'') C1)
      transp-C1'-eq-out = transport (cong (λ B''' → El (⅀ (⅀ A' B'') B''')) C1'-eq-out)

      b-of-RHS : (a : El A') (z : El (B-RHS a)) → El (B'' a)
      b-of-RHS a z = fst (equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) z)

      w-of-RHS : (a : El A') (z : El (B-RHS a)) → El (C1'-out a (b-of-RHS a z))
      w-of-RHS a z = snd (equivFun (⟦⅀⟧ (B'' a) (C1'-out a)) z)

      substed-w-of-RHS : (a : El A') (z : El (B-RHS a))
                       → El (⅀Assoc-C' A' B'' C1'-out (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z)))
      substed-w-of-RHS a z =
        subst (λ p → El (C1'-out (fst p) (snd p)))
              (sym (secEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z)))
              (w-of-RHS a z)

      Assoc-cont-RHS-explicit : (a : El A') (z : El (B-RHS a))
                              → Assoc-cont-RHS a z
                              ≡ invEq (⟦⅀⟧ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
                                      (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , substed-w-of-RHS a z)
      Assoc-cont-RHS-explicit _ _ = refl

      opaque
        transp-C1'-eq-out-on-canonical
          : (a : El A') (z : El (B-RHS a))
          → transp-C1'-eq-out (invEq (⟦⅀⟧ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
                                      (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , substed-w-of-RHS a z))
          ≡ invEq (⟦⅀⟧ (⅀ A' B'') C1)
                  ( invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z)
                  , transport (cong El (funExt⁻ C1'-eq-out (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z))))
                              (substed-w-of-RHS a z))
        transp-C1'-eq-out-on-canonical a z =
            cong (λ e → equivFun e (invEq (⟦⅀⟧ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
                                           (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , substed-w-of-RHS a z)))
                 (⟦⅀⟧-natural-snd 𝒰 (⅀ A' B'') C1'-eq-out)
          ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A' B'') C1)
                              (fst p ,
                               transport (cong El (funExt⁻ C1'-eq-out (fst p))) (snd p)))
                 (secEq (⟦⅀⟧ (⅀ A' B'') (⅀Assoc-C' A' B'' C1'-out))
                        (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , substed-w-of-RHS a z))

      opaque
        key-eq-RHS : (a : El A') (b : El (B'' a))
                   → cong El (funExt⁻ C1'-eq-out (invEq (⟦⅀⟧ A' B'') (a , b)))
                   ≡ cong (λ p → El (C1'-out (fst p) (snd p)))
                          (secEq (⟦⅀⟧ A' B'') (a , b))
        key-eq-RHS a b = cong (cong (λ x → El (C1 x)))
                              (sym (adj-coh (⟦⅀⟧ A' B'') (a , b)))

      opaque
        c'-of-eq-RHS : (a : El A') (z : El (B-RHS a))
                     → w-of-RHS a z
                     ≡ transport (cong El (funExt⁻ C1'-eq-out (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z))))
                                 (substed-w-of-RHS a z)
        c'-of-eq-RHS a z =
            sym (transportRefl (w-of-RHS a z))
          ∙ cong (λ p → transport p (w-of-RHS a z))
                 (sym (lCancel (cong (λ p → El (C1'-out (fst p) (snd p)))
                                      (secEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z)))))
          ∙ cong (λ p → transport (cong (λ p → El (C1'-out (fst p) (snd p)))
                                         (sym (secEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z))) ∙ p)
                                    (w-of-RHS a z))
                 (sym (key-eq-RHS a (b-of-RHS a z)))
          ∙ substComposite (λ X → X)
                           (cong (λ p → El (C1'-out (fst p) (snd p)))
                                 (sym (secEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z))))
                           (cong El (funExt⁻ C1'-eq-out (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z))))
                           (w-of-RHS a z)

      opaque
        transp-⅀AssocD-RHS-on-pair
          : (a : El A') (z : El (B-RHS a))
          → transport (cong El (⅀AssocD 𝒰 A' B'' C1)) (invEq (⟦⅀⟧ A' B-RHS) (a , z))
          ≡ invEq (⟦⅀⟧ (⅀ A' B'') C1)
                  (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , w-of-RHS a z)
        transp-⅀AssocD-RHS-on-pair a z =
            cong (λ p → transport p (invEq (⟦⅀⟧ A' B-RHS) (a , z)))
                 (congFunct El (Inj (⅀Assoc≃ A' B'' C1'-out)) (cong (⅀ (⅀ A' B'')) C1'-eq-out))
          ∙ substComposite (λ X → X)
                           (cong El (Inj (⅀Assoc≃ A' B'' C1'-out)))
                           (cong El (cong (⅀ (⅀ A' B'')) C1'-eq-out))
                           (invEq (⟦⅀⟧ A' B-RHS) (a , z))
          ∙ cong transp-C1'-eq-out (step-Assoc-on-pair-RHS a z ∙ Assoc-cont-RHS-refl a z)
          ∙ cong transp-C1'-eq-out (Assoc-cont-RHS-explicit a z)
          ∙ transp-C1'-eq-out-on-canonical a z
          ∙ cong (λ w → invEq (⟦⅀⟧ (⅀ A' B'') C1)
                              (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a z) , w))
                 (sym (c'-of-eq-RHS a z))

      -- ===== Per-fibre Σ-shuffle (used to compute transport along per-fibre-Δ) =====

      Assoc-cont-per-fibre : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (⅀ (B'' a) (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                            (λ b' b'' → C (paired a b') b'')))
      Assoc-cont-per-fibre a b w =
        invEq (⟦⅀⟧ (B'' a) (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                                (λ b' b'' → C (paired a b') b'')))
              (invEq (Σ-cong-equiv-fst {B = λ p → El (C (paired a (fst p)) (snd p))}
                                        (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))))
                     (invEq Σ-assoc-≃
                            (equivFun (Σ-cong-equiv-snd (λ b' → ⟦⅀⟧ (B (paired a b')) (C (paired a b'))))
                                      (b , w))))

      opaque
        Assoc-cont-per-fibre-refl
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → equivFun (⅀Assoc≃ (B' a) (λ b' → B (paired a b'))
                                      (λ b' b'' → C (paired a b') b''))
                     (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
          ≡ Assoc-cont-per-fibre a b w
        Assoc-cont-per-fibre-refl a b w =
          cong (λ p → invEq (⟦⅀⟧ (B'' a) (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                                              (λ b' b'' → C (paired a b') b'')))
                             (invEq (Σ-cong-equiv-fst {B = λ p → El (C (paired a (fst p)) (snd p))}
                                                       (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))))
                                    (invEq Σ-assoc-≃
                                           (equivFun (Σ-cong-equiv-snd
                                                       (λ b' → ⟦⅀⟧ (B (paired a b')) (C (paired a b')))) p))))
               (secEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))

      opaque
        step-Assoc-on-pair-per-fibre
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → transport (cong El (Inj (⅀Assoc≃ (B' a) (λ b' → B (paired a b'))
                                                      (λ b' b'' → C (paired a b') b''))))
                      (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
          ≡ Assoc-cont-per-fibre a b w
        step-Assoc-on-pair-per-fibre a b w =
            cong (λ p → transport p (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w)))
                 (sym (⟦⅀Assoc⟧ (B' a) (λ b' → B (paired a b'))
                                        (λ b' b'' → C (paired a b') b'')))
          ∙ uaβ (⅀Assoc≃ (B' a) (λ b' → B (paired a b'))
                                  (λ b' b'' → C (paired a b') b''))
                (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
          ∙ Assoc-cont-per-fibre-refl a b w

      -- The explicit Σ-pair form of Assoc-cont-per-fibre at canonical inputs.
      b''-of : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
             → El (B (paired a b))
      b''-of a b w = fst (equivFun (⟦⅀⟧ (B (paired a b)) (C (paired a b))) w)

      c''-of : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
             → El (C (paired a b) (b''-of a b w))
      c''-of a b w = snd (equivFun (⟦⅀⟧ (B (paired a b)) (C (paired a b))) w)

      shifted-c''-per-fibre
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                (λ b' b'' → C (paired a b') b'')
                                 (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)))
      shifted-c''-per-fibre a b w =
        subst (λ p → El (C (paired a (fst p)) (snd p)))
              (sym (secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)))
              (c''-of a b w)

      Assoc-cont-per-fibre-explicit
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → Assoc-cont-per-fibre a b w
        ≡ invEq (⟦⅀⟧ (B'' a) (⅀Assoc-C' (B' a) (λ b' → B (paired a b'))
                                                (λ b' b'' → C (paired a b') b'')))
                (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w) , shifted-c''-per-fibre a b w)
      Assoc-cont-per-fibre-explicit _ _ _ = refl

      -- ===== R1: transport via cong (⅀ A') (funExt per-fibre-Δ). =====

      -- The "inner" snd component of transport (cong El (per-fibre-Δ a)) (invEq ⟦⅀⟧ (b, w)).
      R1-snd-on-pair : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
                     → El (B-RHS a)
      R1-snd-on-pair a b w =
        transport (cong El (per-fibre-Δ a)) (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))

      -- The Σ-pair form of R1-snd-on-pair.
      R1-snd-form
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (B-RHS a)
      R1-snd-form a b w =
        invEq (⟦⅀⟧ (B'' a) (C1'-out a))
              ( invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)
              , transport (cong El (funExt⁻ (snd-adjust-a' a)
                                              (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
                          (shifted-c''-per-fibre a b w))

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
                 (step-Assoc-on-pair-per-fibre a b w ∙ Assoc-cont-per-fibre-explicit a b w)
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

      -- R1 on canonical pair (invEq ⟦⅀⟧ (a, z)).
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

      -- ===== The natural RHS-chain endpoint, RHS-form =====

      RHS-form : (a : El A') (z : El (B-LHS a))
               → El (⅀ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
      RHS-form a z =
        invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
              ( transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a (transport (cong El (per-fibre-Δ a)) z)))
              , w-of-RHS a (transport (cong El (per-fibre-Δ a)) z))

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

      -- ===== Connecting RHS-form to canonical-form (σ-bridge) =====

      -- Per-fibre b''-of, c''-of in terms of an arbitrary z : El (B-LHS a):
      b''-of-z : (a : El A') (z : El (B-LHS a)) → El (B (paired a (b-of-LHS a z)))
      b''-of-z a z = b''-of a (b-of-LHS a z) (w-of-LHS a z)

      c''-of-z : (a : El A') (z : El (B-LHS a))
               → El (C (paired a (b-of-LHS a z)) (b''-of-z a z))
      c''-of-z a z = c''-of a (b-of-LHS a z) (w-of-LHS a z)

      shifted-c''-outer
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (⅀Assoc-C' (⅀ A' B') B C
                         (invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)))
      shifted-c''-outer a b w =
        subst (λ p → El (C (fst p) (snd p)))
              (sym (secEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)))
              (c''-of a b w)

      shifted-c''-outer-z
        : (a : El A') (z : El (B-LHS a))
        → El (⅀Assoc-C' (⅀ A' B') B C
                         (invEq (⟦⅀⟧ (⅀ A' B') B) (paired a (b-of-LHS a z) , b''-of-z a z)))
      shifted-c''-outer-z a z = shifted-c''-outer a (b-of-LHS a z) (w-of-LHS a z)

      -- Canonical-form decomposed.
      canonical-form-explicit
        : (a : El A') (z : El (B-LHS a))
        → canonical-form a z
        ≡ invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
                ( invEq (⟦⅀⟧ (⅀ A' B') B) (paired a (b-of-LHS a z) , b''-of-z a z)
                , shifted-c''-outer-z a z)
      canonical-form-explicit _ _ = refl

      -- transp-⅀AB on canonical pair (a, invEq ⟦⅀⟧ (b, b''))
      -- This is the analog of transp-⅀IdlD used in the leaf case σ-bridge.
      opaque
        transp-⅀AssocD-on-canonical
          : (a : El A') (b : El (B' a)) (b'' : El (B (paired a b)))
          → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b'')))
          ≡ invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b'')
        transp-⅀AssocD-on-canonical a b b'' =
            transp-⅀AB-factored a (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))
          ∙ cong transp-C'-eq (Assoc-cont-explicit a (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b'')))
          ∙ transp-C'-eq-on-canonical a (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))
          ∙ cong (λ p → invEq (⟦⅀⟧ (⅀ A' B') B) (paired a (fst p) , snd p))
                 ( ΣPathP (refl ,
                            sym (c'-of-eq a (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))))
                 ∙ secEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''))

      -- ⟦⅀⟧ applied to R1-snd-form a b w: recovers (q₁, q₂) by secEq.
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

      -- ===== σ-bridge: canonical-form a z ≡ RHS-form a z on canonical pair input =====

      -- The Σ-pair form of canonical-form a (invEq ⟦⅀⟧ (b, w)).
      canonical-form-on-pair-Σ
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → outer-Assoc-cont (paired a b) w
        ≡ invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C))
                ( invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)
                , shifted-c''-outer a b w)
      canonical-form-on-pair-Σ _ _ _ = refl

      -- path1: the Σ-pair form of ⟦⅀⟧ R1-snd-on-pair.
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

      -- Σ-bridge fst-path component.
      opaque
        Σ-bridge-fst
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → invEq (⟦⅀⟧ (⅀ A' B') B) (paired a b , b''-of a b w)
          ≡ transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , b-of-RHS a (R1-snd-on-pair a b w)))
        Σ-bridge-fst a b w =
            sym (transp-⅀AssocD-on-canonical a b (b''-of a b w))
          ∙ cong (λ x → transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , x)))
                 (sym (cong fst (path1 a b w)))

      -- The intermediate Σ-pair at the midpoint of Σ-bridge-fst.
      Σ-bridge-mid-snd
        : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
        → El (⅀Assoc-C' (⅀ A' B') B C
                          (transp-⅀AB (invEq (⟦⅀⟧ A' B'') (a , invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w)))))
      Σ-bridge-mid-snd a b w =
        transport (cong El (funExt⁻ (snd-adjust-a' a)
                                      (invEq (⟦⅀⟧ (B' a) (λ b' → B (paired a b'))) (b , b''-of a b w))))
                  (shifted-c''-per-fibre a b w)

      -- PathP-part2: from Σ-bridge-mid-snd to w-of-RHS R1-snd-on-pair over
      -- cong (λ x → transp-⅀AB (invEq ⟦⅀⟧ (a, x))) (sym (cong fst (path1 a b w))).
      -- Built directly from path1.
      opaque
        Σ-bridge-snd-part2
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → PathP (λ i → El (⅀Assoc-C' (⅀ A' B') B C
                                          (transp-⅀AB (invEq (⟦⅀⟧ A' B'')
                                                              (a , cong fst (path1 a b w) (~ i))))))
                  (Σ-bridge-mid-snd a b w)
                  (w-of-RHS a (R1-snd-on-pair a b w))
        Σ-bridge-snd-part2 a b w = λ i → snd (path1 a b w (~ i))

      -- snd-adjust-a' a is, by definition, a funExt of a 2-factor composition;
      -- funExt⁻ at z' unfolds to that composition.
      opaque
        unfolding snd-adjust-a'
        snd-adjust-on-pair-decomp
          : (a : El A') (z' : El (B'' a))
          → funExt⁻ (snd-adjust-a' a) z'
          ≡ cong C-curry-top (ΣPathP (refl , c'-of-eq a z'))
          ∙ sym (cong C-curry-top (⟦⅀⟧-on-transp a z'))
        snd-adjust-on-pair-decomp _ _ = refl

      -- path-bridge-LHS-to-RHS: the Code-level path equality consumed by
      -- Σ-bridge-snd-part1-endpoint below.  Node-level analog of leaf-case
      -- funExt-q-decomp.  Both sides factor as cong C-curry-top of paths in
      -- Σ (El (⅀ A' B')) (λ ab → El (B ab)); the inner Σ-level equation closes
      -- via a single homotopyNatural application against secEq ⟦⅀⟧ (⅀ A' B') B,
      -- with the leading three segments of transp-⅀AssocD-on-canonical
      -- cancelling against ⟦⅀⟧-on-transp.
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

            -- TAC's four constituent paths (as expressed in the body of
            -- transp-⅀AssocD-on-canonical, which is unfolded here).
            step1 = transp-⅀AB-factored a z'
            step2 = cong transp-C'-eq (Assoc-cont-explicit a z')   -- ≡ refl
            step3 = transp-C'-eq-on-canonical a z'
            step4 = cong (λ p → invEq ⟦⅀⟧' (paired a (fst p) , snd p)) P
            step123 = step1 ∙ step2 ∙ step3

            TAC = transp-⅀AssocD-on-canonical a b (b''-of a b w)

            -- Homotopy `equivFun ⟦⅀⟧' ∘ invEq ⟦⅀⟧' ∘ pfs ~ pfs`.
            H-pfs : (p : Σ (El (B' a)) (λ b' → El (B (paired a b'))))
                  → equivFun ⟦⅀⟧' (invEq ⟦⅀⟧' (pfs p)) ≡ pfs p
            H-pfs p = secEq ⟦⅀⟧' (pfs p)

            -- (1) Reassociate TAC as step123 ∙ step4.
            --     TAC unfolds to step1 ∙ step2 ∙ step3 ∙ step4 (right-assoc).
            TAC-rearrange : TAC ≡ step123 ∙ step4
            TAC-rearrange =
                cong (step1 ∙_) (assoc step2 step3 step4)
              ∙ assoc step1 (step2 ∙ step3) step4

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

      -- Mirror of leaf-case endpoint-fix (lines 625-640), one Σ-level up.
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

      -- ===== bridge-node assembly (standard InjSec sandwich) =====

      opaque
        unfolding Σ-bridge-fst
        σ-bridge-on-pair
          : (a : El A') (b : El (B' a)) (w : El (C'-out a b))
          → outer-Assoc-cont (paired a b) w
          ≡ RHS-form a (invEq (⟦⅀⟧ (B' a) (C'-out a)) (b , w))
        σ-bridge-on-pair a b w =
          cong (invEq (⟦⅀⟧ (⅀ (⅀ A' B') B) (⅀Assoc-C' (⅀ A' B') B C)))
               (ΣPathP (Σ-bridge-fst a b w
                       , compPathP' {B = λ x → El (⅀Assoc-C' (⅀ A' B') B C x)}
                                    (toPathP (Σ-bridge-snd-part1-endpoint a b w))
                                    (Σ-bridge-snd-part2 a b w)))

      opaque
        σ-bridge-base
          : (a : El A') (z : El (B-LHS a))
          → canonical-form a z ≡ RHS-form a z
        σ-bridge-base a z =
            σ-bridge-on-pair a (b-of-LHS a z) (w-of-LHS a z)
          ∙ cong (RHS-form a) (retEq (⟦⅀⟧ (B' a) (C'-out a)) z)

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

      equivs-agree-node : pathToEquiv (cong El LHS-path)
                        ≡ pathToEquiv (cong El (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail))
      equivs-agree-node = equivEq (funExt pointwise-node)

      opaque
        bridge-node : LHS-path ≡ cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail
        bridge-node =
            sym (InjSec 𝒰 LHS-path)
          ∙ cong Inj equivs-agree-node
          ∙ InjSec 𝒰 (cong (⅀ A') (funExt per-fibre-Δ) ∙ RHS-path-tail)

      -- eq-node final chain: six substComposite/cong/graft-subst-fst steps that
      -- glue together (a)–(e) into the LHS ≡ RHS transport.
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
  -- Set case: PathP into the set FreeOps K (⅀ (⅀ A B) (⅀Assoc-C' A B C)) is
  -- a proposition; fill the square via isProp→SquareP.
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

  -- The free 𝒰-operad on K, assembled from the three laws above.
  isSetFreeOps : (K : Code → Type ℓk) (A : Code) → isSet (FreeOps K A)
  isSetFreeOps K A = set A

  FreeOperad : (K : Code → Type ℓk) → Operad 𝒰 (FreeOps K)
  Operad.isSetK (FreeOperad K) = isSetFreeOps K
  Operad.id     (FreeOperad K) = leaf
  Operad.compₒ  (FreeOperad K) = graft K
  Operad.idl    (FreeOperad K) = graft-idl K
  Operad.idr    (FreeOperad K) = graft-idr K
  Operad.assoc  (FreeOperad K) = graft-assoc K
