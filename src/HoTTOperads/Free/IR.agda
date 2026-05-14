{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Free.IR
--
-- Operad structure on the inductive-recursive free operad
-- `FreeOps' K A = Fiber K A`, with `compₒ` defined as the *direct* IR
-- `graft` (FreeOperad.tex §9 lines 280-294) — not as a transport of the HIT
-- `graft` across the fiber equivalence.
--
-- Layout:
--   §1   Direct IR graft `graftFib`, defined by structural recursion on the
--        IR tree (with `J` on the path component of the input fiber).
--   §2   Two pushing lemmas (`to-subst-FreeOps`, `to-node-eq`) for the
--        agreement proof.
--   §3   Agreement lemma: `graftFib` equals the HIT graft viewed under the
--        equivalence `to / from`.
--   §4   Operad laws `idl-fib`, `idr-fib`, `assoc-fib`, each obtained by
--        applying `to` pointwise to the corresponding HIT law and rewriting
--        the endpoints via the agreement lemma and `section`.
--   §5   Operad assembly `FreeOperad : Operad 𝒰 (FreeOps' K)`.
--
-- This module also re-exports `HoTTOperads.Free.IR.Base` and
-- `HoTTOperads.Free.IR.FiberEquiv` so downstream modules can keep importing
-- `HoTTOperads.Free.IR` unchanged.
-- ============================================================================
module HoTTOperads.Free.IR where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (invEq ; secEq ; retEq ; equivFun)
open import Cubical.Foundations.GroupoidLaws using (rUnit ; lUnit)
open import Cubical.Foundations.Path using (isProp→SquareP)
open import Cubical.Data.Sigma using (_,_ ; fst ; snd ; Σ ; Σ-syntax ; ΣPathP)
open import Cubical.Data.Unit using (tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.IRDerived
open import HoTTOperads.Operad.Base

open import HoTTOperads.Free.IR.Base       public
open import HoTTOperads.Free.IR.FiberEquiv public
import HoTTOperads.Free.HIT as HIT

private
  variable
    ℓc ℓe ℓk : Level

module _ {𝒰 : Universe ℓc ℓe} (K : Universe.Code 𝒰 → Type ℓk) where
  open Universe 𝒰

  -- ============================================================================
  -- §1  Direct IR graft
  --
  -- `graft t C tss` is the paper's `graft` (FreeOperad.tex 280-294) at
  -- index `CodeOp t`. It is defined by structural recursion on `t`, with the
  -- `set` case filled by `isSet→SquareP` after η-expansion in the (C, tss)
  -- arguments — the result type at each cube vertex is a Π-into-`Fiber`,
  -- which is a set by `isSetFiberCodeOp`.
  --
  -- The operad-shaped `graftFib` reduces the general `(t, p) : Fiber A` input
  -- to the `p ≡ refl` base via `J`.
  -- ============================================================================
  graft : (t : FreeOpsIR {𝒰 = 𝒰} K)
              → (C : El (CodeOp {𝒰 = 𝒰} K t) → Code)
              → ((a : El (CodeOp {𝒰 = 𝒰} K t)) → Fiber {𝒰 = 𝒰} K (C a))
              → Fiber {𝒰 = 𝒰} K (⅀ (CodeOp {𝒰 = 𝒰} K t) C)
  graft leaf C tss =
    let α = invEq ⟦𝜏⟧ tt
    in  (fst (tss α) , snd (tss α) ∙ ⅀IdlD 𝒰 C)
  graft (node A' k ts') C tss =
    let iv : Σ (El A') (λ a → El (CodeOp {𝒰 = 𝒰} K (ts' a)))
           → El (⅀ A' (CodeOp {𝒰 = 𝒰} K ∘ ts'))
        iv = invEq (⟦⅀⟧ A' (CodeOp {𝒰 = 𝒰} K ∘ ts'))
        us : (a : El A')
           → Fiber {𝒰 = 𝒰} K (⅀ (CodeOp {𝒰 = 𝒰} K (ts' a)) (λ b → C (iv (a , b))))
        us a = graft (ts' a)
                           (λ b → C (iv (a , b)))
                           (λ b → tss (iv (a , b)))
    in  ( node A' k (λ a → fst (us a))
        , cong (⅀ A') (funExt (λ a → snd (us a)))
          ∙ ⅀AssocD 𝒰 A' (CodeOp {𝒰 = 𝒰} K ∘ ts') C
        )
  graft (set t u p q s i j) =
    isSet→SquareP
      {A = λ i' j' →
        (C : El (s j' i') → Code)
        (tss : (a : El (s j' i')) → Fiber {𝒰 = 𝒰} K (C a))
      → Fiber {𝒰 = 𝒰} K (⅀ (s j' i') C)}
      (λ _ _ → isSetΠ (λ _ → isSetΠ (λ _ → isSetFiberCodeOp {𝒰 = 𝒰} K _)))
      (λ j' → graft (p j'))
      (λ j' → graft (q j'))
      (λ _  → graft t)
      (λ _  → graft u)
      i j

  graftFib : (A : Code) (C : El A → Code)
           → Fiber {𝒰 = 𝒰} K A
           → ((a : El A) → Fiber {𝒰 = 𝒰} K (C a))
           → Fiber {𝒰 = 𝒰} K (⅀ A C)
  graftFib A C (t , p) tss =
    J (λ A' p' → (C' : El A' → Code)
               → ((a : El A') → Fiber {𝒰 = 𝒰} K (C' a))
               → Fiber {𝒰 = 𝒰} K (⅀ A' C'))
      (graft t) p C tss

  -- ============================================================================
  -- §2  Pushing-lemmas used by the agreement proof
  --
  -- `to-subst-FreeOps`: applying `to B` to a `subst (FreeOps K) p`-transported
  -- tree shifts the path into the snd component of the Σ-pair (composing on the
  -- right with `p`). Proved by `J` on `p`; at `p = refl` the LHS reduces via
  -- `substRefl` and the RHS unit law follows from `rUnit`.
  --
  -- (No separate `to-node-eq` is needed: the `node` clause of `to` is already
  -- definitionally `(node A k …fst… , cong (⅀ A) (funExt …snd…))`.)
  -- ============================================================================
  to-subst-FreeOps : {A B : Code} (p : A ≡ B) (x : HIT.FreeOps {𝒰 = 𝒰} K A)
                   → to K B (subst (HIT.FreeOps {𝒰 = 𝒰} K) p x)
                   ≡ (fst (to K A x) , snd (to K A x) ∙ p)
  to-subst-FreeOps {A} {B} p x =
    J (λ B' p' → to K B' (subst (HIT.FreeOps {𝒰 = 𝒰} K) p' x)
              ≡ (fst (to K A x) , snd (to K A x) ∙ p'))
      base-refl p
    where
      base-refl : to K A (subst (HIT.FreeOps {𝒰 = 𝒰} K) refl x)
                ≡ (fst (to K A x) , snd (to K A x) ∙ refl)
      base-refl = cong (to K A) (substRefl {B = HIT.FreeOps {𝒰 = 𝒰} K} x)
                ∙ λ i → (fst (to K A x) , rUnit (snd (to K A x)) i)

  -- ============================================================================
  -- §3  Agreement of the IR graft with the HIT graft under the equivalence
  --
  -- `graft-agreement` says: applying `graftFib` is the same as transporting
  -- the input fibres into the HIT presentation, running the HIT `graft`,
  -- and transporting the result back via `to`. The proof reduces along
  -- `snd ft : CodeOp _ ≡ A` (via J) and then inducts on the IR tree.
  --
  -- We package the HIT-side RHS in an `opaque` block so that Agda's fast
  -- reducer does not have to unfold `HIT.graft K X C (g K (set …)) …` when
  -- type-checking the `set` clause of `graft-agreement-refl` (which would
  -- trigger an internal error inside `Reduce.Fast` when the cube boundary is
  -- itself a SquareP-filler).
  -- ============================================================================
  opaque
    HIT-graft-via-Fib :
        (t : FreeOpsIR {𝒰 = 𝒰} K)
        (C : El (CodeOp {𝒰 = 𝒰} K t) → Code)
        (tss : (a : El (CodeOp {𝒰 = 𝒰} K t)) → Fiber {𝒰 = 𝒰} K (C a))
      → Fiber {𝒰 = 𝒰} K (⅀ (CodeOp {𝒰 = 𝒰} K t) C)
    HIT-graft-via-Fib t C tss =
      to K (⅀ (CodeOp {𝒰 = 𝒰} K t) C)
           (HIT.graft K (CodeOp {𝒰 = 𝒰} K t) C (g K t)
                        (λ a → from K (C a) (tss a)))

    HIT-graft-via-Fib-unfold :
        (t : FreeOpsIR {𝒰 = 𝒰} K)
        (C : El (CodeOp {𝒰 = 𝒰} K t) → Code)
        (tss : (a : El (CodeOp {𝒰 = 𝒰} K t)) → Fiber {𝒰 = 𝒰} K (C a))
      → HIT-graft-via-Fib t C tss
      ≡ to K (⅀ (CodeOp {𝒰 = 𝒰} K t) C)
             (HIT.graft K (CodeOp {𝒰 = 𝒰} K t) C (g K t)
                          (λ a → from K (C a) (tss a)))
    HIT-graft-via-Fib-unfold _ _ _ = refl

  graft-agreement-refl :
      (t : FreeOpsIR {𝒰 = 𝒰} K) (C : El (CodeOp {𝒰 = 𝒰} K t) → Code)
      (tss : (a : El (CodeOp {𝒰 = 𝒰} K t)) → Fiber {𝒰 = 𝒰} K (C a))
    → graft t C tss ≡ HIT-graft-via-Fib t C tss
  graft-agreement-refl leaf C tss =
       (λ i → (fst (sec (~ i)) , snd (sec (~ i)) ∙ ⅀IdlD 𝒰 C))
     ∙ sym (to-subst-FreeOps (⅀IdlD 𝒰 C) (from K (C α) (tss α)))
     ∙ sym (HIT-graft-via-Fib-unfold leaf C tss)
    where
      α : El 𝜏
      α = invEq ⟦𝜏⟧ tt
      sec : to K (C α) (from K (C α) (tss α)) ≡ tss α
      sec = section K (C α) (tss α)
  graft-agreement-refl (node A' k ts') C tss =
      (λ i → ( node A' k (λ a → fst (agree a i))
             , cong (⅀ A') (funExt (λ a → snd (agree a i)))
               ∙ ⅀AssocD 𝒰 A' (CodeOp {𝒰 = 𝒰} K ∘ ts') C
             ))
    ∙ sym (to-subst-FreeOps
            (⅀AssocD 𝒰 A' (CodeOp {𝒰 = 𝒰} K ∘ ts') C)
            (HIT.node A' B' k
              (λ a → HIT.graft K (CodeOp {𝒰 = 𝒰} K (ts' a))
                                  (λ b → C (iv (a , b)))
                                  (g K (ts' a))
                                  (λ b → from K (C (iv (a , b))) (tss (iv (a , b)))))))
    ∙ sym (HIT-graft-via-Fib-unfold (node A' k ts') C tss)
    where
      iv : Σ (El A') (λ a → El (CodeOp {𝒰 = 𝒰} K (ts' a)))
         → El (⅀ A' (CodeOp {𝒰 = 𝒰} K ∘ ts'))
      iv = invEq (⟦⅀⟧ A' (CodeOp {𝒰 = 𝒰} K ∘ ts'))
      B' : El A' → Code
      B' a = ⅀ (CodeOp {𝒰 = 𝒰} K (ts' a)) (λ b → C (iv (a , b)))
      agree : (a : El A')
            → graft (ts' a) (λ b → C (iv (a , b))) (λ b → tss (iv (a , b)))
            ≡ to K (B' a) (HIT.graft K (CodeOp {𝒰 = 𝒰} K (ts' a))
                                       (λ b → C (iv (a , b)))
                                       (g K (ts' a))
                                       (λ b → from K (C (iv (a , b))) (tss (iv (a , b)))))
      agree a = graft-agreement-refl (ts' a)
                                     (λ b → C (iv (a , b)))
                                     (λ b → tss (iv (a , b)))
                              ∙ HIT-graft-via-Fib-unfold (ts' a)
                                                          (λ b → C (iv (a , b)))
                                                          (λ b → tss (iv (a , b)))
  graft-agreement-refl (set t u p q sq i j) =
    isSet→SquareP
      {A = λ i' j' →
        (C : El (sq j' i') → Code)
        (tss : (a : El (sq j' i')) → Fiber {𝒰 = 𝒰} K (C a))
      → graft (set t u p q sq i' j') C tss
      ≡ HIT-graft-via-Fib (set t u p q sq i' j') C tss}
      (λ _ _ → isSetΠ (λ _ → isSetΠ (λ _ →
                 isProp→isSet (isSetFiberCodeOp {𝒰 = 𝒰} K _ _ _))))
      (λ k → graft-agreement-refl (p k))
      (λ k → graft-agreement-refl (q k))
      (λ _ → graft-agreement-refl t)
      (λ _ → graft-agreement-refl u)
      i j

  -- General agreement: lifts `graft-agreement-refl` along the path component
  -- of the input fibre via `J`. The endpoint at `p = refl` matches the
  -- refl-base after a `JRefl`/`substRefl` chain.
  graft-agreement :
      (A : Code) (C : El A → Code)
      (ft : Fiber {𝒰 = 𝒰} K A) (tss : (a : El A) → Fiber {𝒰 = 𝒰} K (C a))
    → graftFib A C ft tss
    ≡ to K (⅀ A C)
           (HIT.graft K A C (from K A ft) (λ a → from K (C a) (tss a)))
  graft-agreement A C (t , p) tss =
    J (λ A' p' → (C' : El A' → Code)
                 (tss' : (a : El A') → Fiber {𝒰 = 𝒰} K (C' a))
               → graftFib A' C' (t , p') tss'
               ≡ to K (⅀ A' C')
                      (HIT.graft K A' C' (from K A' (t , p'))
                                   (λ a → from K (C' a) (tss' a))))
      step p C tss
    where
      motiveJ : Code → Type _
      motiveJ A' = (C' : El A' → Code)
                 → ((a : El A') → Fiber {𝒰 = 𝒰} K (C' a))
                 → Fiber {𝒰 = 𝒰} K (⅀ A' C')

      step : (C' : El (CodeOp {𝒰 = 𝒰} K t) → Code)
             (tss' : (a : El (CodeOp {𝒰 = 𝒰} K t)) → Fiber {𝒰 = 𝒰} K (C' a))
           → graftFib (CodeOp {𝒰 = 𝒰} K t) C' (t , refl) tss'
           ≡ to K (⅀ (CodeOp {𝒰 = 𝒰} K t) C')
                  (HIT.graft K (CodeOp {𝒰 = 𝒰} K t) C'
                               (from K (CodeOp {𝒰 = 𝒰} K t) (t , refl))
                               (λ a → from K (C' a) (tss' a)))
      step C' tss' =
          (λ i → JRefl (λ A' _ → motiveJ A') (graft t) i C' tss')
        ∙ graft-agreement-refl t C' tss'
        ∙ HIT-graft-via-Fib-unfold t C' tss'
        ∙ (λ i → to K (⅀ (CodeOp {𝒰 = 𝒰} K t) C')
                       (HIT.graft K (CodeOp {𝒰 = 𝒰} K t) C'
                                    (substRefl {B = HIT.FreeOps {𝒰 = 𝒰} K} (g K t) (~ i))
                                    (λ a → from K (C' a) (tss' a))))

  -- ============================================================================
  -- §4  Operad laws on `graftFib`
  --
  -- Each law is the corresponding HIT law applied pointwise via `to`, with
  -- the endpoints rewritten by `graft-agreement` (on the LHS) and `section`
  -- (on the RHS). The double-whiskering operator `_◁_▷_` from Cubical's
  -- Prelude glues the LHS path, the HIT PathP, and the RHS path into a
  -- single PathP in `Fiber K`.
  -- ============================================================================
  private
    from-leaf-eq : from K 𝜏 (leaf , refl) ≡ HIT.leaf
    from-leaf-eq = substRefl {B = HIT.FreeOps {𝒰 = 𝒰} K} HIT.leaf

  idl-fib : (A : Code) (ft : Fiber {𝒰 = 𝒰} K A)
          → PathP (λ i → Fiber {𝒰 = 𝒰} K (Inj (⅀Idl≃ A) i))
                  (graftFib 𝜏 (λ _ → A) (leaf , refl) (λ _ → ft)) ft
  idl-fib A ft =
        lhs-eq
      ◁ (λ i → to K (Inj (⅀Idl≃ A) i) (HIT.graft-idl K A (from K A ft) i))
      ▷ section K A ft
    where
      lhs-eq : graftFib 𝜏 (λ _ → A) (leaf , refl) (λ _ → ft)
             ≡ to K (⅀ 𝜏 (λ _ → A))
                    (HIT.graft K 𝜏 (λ _ → A) HIT.leaf (λ _ → from K A ft))
      lhs-eq =
          graft-agreement 𝜏 (λ _ → A) (leaf , refl) (λ _ → ft)
        ∙ (λ i → to K (⅀ 𝜏 (λ _ → A))
                       (HIT.graft K 𝜏 (λ _ → A)
                                    (from-leaf-eq i)
                                    (λ _ → from K A ft)))

  idr-fib : (A : Code) (ft : Fiber {𝒰 = 𝒰} K A)
          → PathP (λ i → Fiber {𝒰 = 𝒰} K (Inj (⅀Idr≃ A) i))
                  (graftFib A (λ _ → 𝜏) ft (λ _ → (leaf , refl))) ft
  idr-fib A ft =
        lhs-eq
      ◁ (λ i → to K (Inj (⅀Idr≃ A) i) (HIT.graft-idr K A (from K A ft) i))
      ▷ section K A ft
    where
      lhs-eq : graftFib A (λ _ → 𝜏) ft (λ _ → (leaf , refl))
             ≡ to K (⅀ A (λ _ → 𝜏))
                    (HIT.graft K A (λ _ → 𝜏) (from K A ft) (λ _ → HIT.leaf))
      lhs-eq =
          graft-agreement A (λ _ → 𝜏) ft (λ _ → (leaf , refl))
        ∙ (λ i → to K (⅀ A (λ _ → 𝜏))
                       (HIT.graft K A (λ _ → 𝜏)
                                    (from K A ft)
                                    (λ _ → from-leaf-eq i)))

  -- `from ∘ graftFib ≡ HIT.graft ∘ from` (pointwise). Follows from
  -- `graft-agreement` plus the `retract` half of the fiber equivalence.
  from-graftFib :
      (A : Code) (C : El A → Code)
      (ft : Fiber {𝒰 = 𝒰} K A) (tss : (a : El A) → Fiber {𝒰 = 𝒰} K (C a))
    → from K (⅀ A C) (graftFib A C ft tss)
    ≡ HIT.graft K A C (from K A ft) (λ a → from K (C a) (tss a))
  from-graftFib A C ft tss =
      cong (from K (⅀ A C)) (graft-agreement A C ft tss)
    ∙ retract K (⅀ A C)
              (HIT.graft K A C (from K A ft) (λ a → from K (C a) (tss a)))

  assoc-fib :
      (A : Code) (B : El A → Code)
      (C : (a : El A) → El (B a) → Code)
      (ft : Fiber {𝒰 = 𝒰} K A)
      (fts : (a : El A) → Fiber {𝒰 = 𝒰} K (B a))
      (ftss : (a : El A) (b : El (B a)) → Fiber {𝒰 = 𝒰} K (C a b))
    → PathP (λ i → Fiber {𝒰 = 𝒰} K (Inj (⅀Assoc≃ A B C) i))
            (graftFib A (λ a → ⅀ (B a) (C a)) ft
                      (λ a → graftFib (B a) (C a) (fts a) (ftss a)))
            (graftFib (⅀ A B) (⅀Assoc-C' A B C)
                      (graftFib A B ft fts)
                      (λ ab → ftss (fst (equivFun (⟦⅀⟧ A B) ab))
                                    (snd (equivFun (⟦⅀⟧ A B) ab))))
  assoc-fib A B C ft fts ftss =
        lhs-eq
      ◁ (λ i → to K (Inj (⅀Assoc≃ A B C) i)
                     (HIT.graft-assoc K A B C
                                       (from K A ft)
                                       (λ a → from K (B a) (fts a))
                                       (λ a b → from K (C a b) (ftss a b)) i))
      ▷ sym rhs-eq
    where
      -- Inner per-a `from`-of-`graftFib` rewriting, used in the LHS chain.
      inner-eq : (a : El A)
               → from K (⅀ (B a) (C a)) (graftFib (B a) (C a) (fts a) (ftss a))
               ≡ HIT.graft K (B a) (C a)
                              (from K (B a) (fts a))
                              (λ b → from K (C a b) (ftss a b))
      inner-eq a = from-graftFib (B a) (C a) (fts a) (ftss a)

      lhs-eq : graftFib A (λ a → ⅀ (B a) (C a)) ft
                        (λ a → graftFib (B a) (C a) (fts a) (ftss a))
             ≡ to K (⅀ A (λ a → ⅀ (B a) (C a)))
                    (HIT.graft K A (λ a → ⅀ (B a) (C a))
                                 (from K A ft)
                                 (λ a → HIT.graft K (B a) (C a)
                                                    (from K (B a) (fts a))
                                                    (λ b → from K (C a b) (ftss a b))))
      lhs-eq =
          graft-agreement A (λ a → ⅀ (B a) (C a)) ft
                          (λ a → graftFib (B a) (C a) (fts a) (ftss a))
        ∙ (λ i → to K (⅀ A (λ a → ⅀ (B a) (C a)))
                       (HIT.graft K A (λ a → ⅀ (B a) (C a))
                                    (from K A ft)
                                    (λ a → inner-eq a i)))

      -- Outer `from`-of-`graftFib` rewriting, used in the RHS chain.
      outer-eq : from K (⅀ A B) (graftFib A B ft fts)
               ≡ HIT.graft K A B (from K A ft) (λ a → from K (B a) (fts a))
      outer-eq = from-graftFib A B ft fts

      rhs-eq : graftFib (⅀ A B) (⅀Assoc-C' A B C)
                        (graftFib A B ft fts)
                        (λ ab → ftss (fst (equivFun (⟦⅀⟧ A B) ab))
                                      (snd (equivFun (⟦⅀⟧ A B) ab)))
             ≡ to K (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                    (HIT.graft K (⅀ A B) (⅀Assoc-C' A B C)
                                 (HIT.graft K A B (from K A ft)
                                              (λ a → from K (B a) (fts a)))
                                 (λ ab → from K (⅀Assoc-C' A B C ab)
                                                (ftss (fst (equivFun (⟦⅀⟧ A B) ab))
                                                      (snd (equivFun (⟦⅀⟧ A B) ab)))))
      rhs-eq =
          graft-agreement (⅀ A B) (⅀Assoc-C' A B C)
                          (graftFib A B ft fts)
                          (λ ab → ftss (fst (equivFun (⟦⅀⟧ A B) ab))
                                        (snd (equivFun (⟦⅀⟧ A B) ab)))
        ∙ (λ i → to K (⅀ (⅀ A B) (⅀Assoc-C' A B C))
                       (HIT.graft K (⅀ A B) (⅀Assoc-C' A B C)
                                    (outer-eq i)
                                    (λ ab → from K (⅀Assoc-C' A B C ab)
                                                   (ftss (fst (equivFun (⟦⅀⟧ A B) ab))
                                                         (snd (equivFun (⟦⅀⟧ A B) ab))))))

  -- ============================================================================
  -- §5  Operad assembly
  --
  -- The free 𝒰-operad on `K`, presented on the IR fibres `FreeOps' K`. The
  -- composition `compₒ` is the direct IR `graftFib`; the laws are derived
  -- (via `graft-agreement`) from the corresponding HIT laws.
  -- ============================================================================
  FreeOperad : Operad 𝒰 (FreeOps' {𝒰 = 𝒰} K)
  Operad.isSetK FreeOperad = isSetFiberCodeOp {𝒰 = 𝒰} K
  Operad.id     FreeOperad = (leaf , refl)
  Operad.compₒ  FreeOperad = graftFib
  Operad.idl    FreeOperad = idl-fib
  Operad.idr    FreeOperad = idr-fib
  Operad.assoc  FreeOperad = assoc-fib

