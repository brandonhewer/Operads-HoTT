{-# OPTIONS --cubical #-}
module HoTTOperads.Universe.Instances.Nat where

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
  ; sum≡sum-prefix-ℕ ; inj-l-+ ; inj-r-+ )

-- Fin1≃Unit kept transparent: equivalence value, .equiv-proof is consumed downstream.
Fin1≃Unit : Fin 1 ≃ Unit
Fin1≃Unit = isoToEquiv (isContr→Iso isContrFin1 (tt , λ _ → refl))

opaque
  NatInj : {n m : ℕ} → Fin n ≃ Fin m → n ≡ m
  NatInj {n} {m} e = Fin-inj n m (ua e)

  NatInjComp : {n m k : ℕ} (e₁ : Fin n ≃ Fin m) (e₂ : Fin m ≃ Fin k)
             → NatInj (compEquiv e₁ e₂) ≡ NatInj e₁ ∙ NatInj e₂
  NatInjComp _ _ = isSetℕ _ _ _ _

-- The base (non-coherent) part.
𝓝-base : UniverseBase ℓ-zero ℓ-zero
UniverseBase.Code     𝓝-base = ℕ
UniverseBase.El       𝓝-base = Fin
UniverseBase.⅀        𝓝-base = sum
UniverseBase.𝜏        𝓝-base = 1
UniverseBase.⟦⅀⟧      𝓝-base = sumFinEquiv
UniverseBase.⟦𝜏⟧      𝓝-base = Fin1≃Unit
UniverseBase.Inj      𝓝-base = NatInj
UniverseBase.InjComp  𝓝-base = NatInjComp

------------------------------------------------------------------------
-- Coherences.
--
-- Strategy: each `e ∈ {⅀Idl≃ A, ⅀Idr≃ A, ⅀Assoc≃ A B C}` is shown to
-- preserve the underlying ℕ-index (i.e. `fst ∘ equivFun e ≡ fst`).
-- Then equivFin-by-fst lifts that to `e ≡ pathToEquiv (cong Fin p)` for
-- any path p : n ≡ m, and `ua-pathToEquiv` collapses the coherence
-- statement to a path between ℕ-paths, killed by `isSetℕ`.
------------------------------------------------------------------------

open UniverseBase 𝓝-base using (⅀Idl≃ ; ⅀Idr≃ ; ⅀Assoc≃ ; ⅀Assoc-C')

opaque
  -- Boilerplate: convert an fst-preservation proof into a single
  -- coherence. The chosen `p : n ≡ m` is immaterial since ℕ is a set.
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

  ------------------------------------------------------------------------
  -- Idl: ⅀Idl≃ A : Fin (A + 0) ≃ Fin A preserves the ℕ-index.
  ------------------------------------------------------------------------

  ⅀Idl-preserves-fst : (A : ℕ) (k : Fin (sum 1 (λ _ → A)))
                     → fst (equivFun (⅀Idl≃ A) k) ≡ fst k
  ⅀Idl-preserves-fst A (m , p) with m ≤? A
  ... | inl _    = refl
  ... | inr m≥A  = ⊥-rec (¬m<m (≤<-trans m≥A (subst (m <_) (+-zero A) p)))

  ------------------------------------------------------------------------
  -- Idr: ⅀Idr≃ A : Fin (sum A (λ _ → 1)) ≃ Fin A preserves the ℕ-index.
  ------------------------------------------------------------------------

  ⅀Idr-preserves-fst : (A : ℕ) (k : Fin (sum A (λ _ → 1)))
                     → fst (equivFun (⅀Idr≃ A) k) ≡ fst k
  ⅀Idr-preserves-fst zero      (_     , p)   = ⊥-rec (¬-<-zero p)
  ⅀Idr-preserves-fst (suc A)   (zero  , p) with zero ≤? 1
  ... | inl _ = refl
  ... | inr 1≤0 = ⊥-rec (¬-<-zero 1≤0)
  ⅀Idr-preserves-fst (suc A)   (suc m , p) with suc m ≤? 1
  ... | inl sm<1 = ⊥-rec (¬-<-zero (pred-≤-pred sm<1))
  ... | inr _    = cong suc (⅀Idr-preserves-fst A _)

------------------------------------------------------------------------
-- Assoc: hardest case. The lexicographic flatten is associative.
------------------------------------------------------------------------

-- Associativity preservation: the lexicographic flatten is associative.
-- Strategy: trace `invEq (⅀Assoc≃ A B C)` through its 5 composed steps;
-- this gives a definitional reduction of `fst` to a left-associated
-- arithmetic expression. The forward direction follows via `retEq`.

------------------------------------------------------------------------
-- Fubini identity.
--
-- The lexicographic flatten `sumFinBwd A B (a, b)` lands at flat index
-- `sum-prefix A B a + fst b`. Applying `sum-prefix` of the linearized
-- C-array to that index splits as the "full first-block" portion (a
-- full `sum (B a') (C a')` for each `a' < a`) plus the "partial b"
-- portion (a prefix sum of `C a`).
------------------------------------------------------------------------

private
  opaque
    -- A specialized rephrasing of the "fst preservation" facts about
    -- sumFinFwd, used inside fubini's inl branch.
    sumFinFwd-inl-fst : (A' : ℕ) (B : Fin (suc A') → ℕ) (i : Fin (B fzero))
                      (klt : fst i < B fzero + sum A' (B ∘ fsuc))
                      → fst (sumFinFwd (suc A') B (fst i , klt)) ≡ 0
    sumFinFwd-inl-fst A' B (k , k<m) klt with k ≤? B fzero
    ... | inl _ = refl
    ... | inr B≤k = ⊥-rec (¬m<m (≤<-trans B≤k k<m))

    -- And the corresponding 2nd coord lookup as a ℕ.
    sumFinFwd-inl-snd : (A' : ℕ) (B : Fin (suc A') → ℕ) (i : Fin (B fzero))
                      (klt : fst i < B fzero + sum A' (B ∘ fsuc))
                      → fst (snd (sumFinFwd (suc A') B (fst i , klt))) ≡ fst i
    sumFinFwd-inl-snd A' B (k , k<m) klt with k ≤? B fzero
    ... | inl _ = refl
    ... | inr B≤k = ⊥-rec (¬m<m (≤<-trans B≤k k<m))

-- Helper: prefix-sum of a function defined via sumFinFwd at "inl-region"
-- indices reduces to prefix-sum of C fzero.  Exposed publicly so IExpr.agda
-- (which builds the (m+n)-level analogues) can re-use it.
opaque
  ⅀Assoc-C'-on-inl : (A' : ℕ) (B : Fin (suc A') → ℕ)
                     (C : (a : Fin (suc A')) → Fin (B a) → ℕ)
                     (i : Fin (B fzero))
                   → ⅀Assoc-C' (suc A') B C
                       (inj-l-+ (B fzero) (sum A' (B ∘ fsuc)) i)
                   ≡ C fzero i
  ⅀Assoc-C'-on-inl A' B C (k , k<m) with k ≤? B fzero
  ... | inl _   = cong (C fzero) (Fin-fst-≡ refl)
  ... | inr B≤k = ⊥-rec (¬m<m (≤<-trans B≤k k<m))

  -- Symmetric for the inr-region: ⅀Assoc-C' at (B fzero + fst i, _) reduces
  -- to applying C ∘ fsuc to the lex decomposition in the sub-problem.
  ⅀Assoc-C'-on-inr : (A' : ℕ) (B : Fin (suc A') → ℕ)
                     (C : (a : Fin (suc A')) → Fin (B a) → ℕ)
                     (i : Fin (sum A' (B ∘ fsuc)))
                   → ⅀Assoc-C' (suc A') B C
                       (inj-r-+ (B fzero) (sum A' (B ∘ fsuc)) i)
                   ≡ ⅀Assoc-C' A' (B ∘ fsuc) (λ a' → C (fsuc a')) i
  ⅀Assoc-C'-on-inr A' B C (k , klt) with (B fzero + k) ≤? B fzero
  ... | inl B+k<B  = ⊥-rec (¬m+n<m {m = B fzero} {n = k} B+k<B)
    where
      open import Cubical.Data.Nat.Order using (¬m+n<m)
  ... | inr B≤B+k  =
    -- sumFinFwd recurses on ((B fzero + k) ∸ B fzero, _) which equals (k, _) propositionally.
    cong (λ x → C (fsuc (fst x)) (snd x))
         (cong (sumFinFwd A' (B ∘ fsuc))
               (Fin-fst-≡ ((cong (_∸ B fzero) (+-comm (B fzero) k))
                          ∙ m+n∸n=m (B fzero) k)))
    where
      open import Cubical.Data.Fin.Properties using (m+n∸n=m)

{-
-- (m+n)-level Fubini analogues of ⅀Assoc-C'-on-inl / ⅀Assoc-C'-on-inr,
-- proven by induction on m using the suc-level versions.
-- Reserved here for documentation. Implementation will go in IExpr.agda
-- where `sum-split` is available and the bound-bridging via subst Fin is cleaner.

opaque
  unfolding ⅀Assoc-C'-on-inl ⅀Assoc-C'-on-inr

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
  ... | inl k<B0  | inl k<Bₗ0 =
    -- Both reduce: LHS = C fzero (k , k<B0), RHS = (C ∘ inj-l-+) fzero (k , k<Bₗ0).
    -- The Fin element differs in type (Fin (B fzero) vs Fin (B (inj-l-+ ...))), so we
    -- build a PathP via ΣPathP using refl on fst and isProp→PathP on the bound.
    let
      fz-path : (fzero {k = m' + n}) ≡ inj-l-+ (suc m') n fzero
      fz-path = Fin-fst-≡ refl
      sn-path : PathP (λ j → Fin (B (fz-path j))) (k , k<B0) (k , k<Bₗ0)
      sn-path = ΣPathP (refl , isProp→PathP (λ _ → isProp≤) k<B0 k<Bₗ0)
    in λ i → C (fz-path i) (sn-path i)
  ... | inl k<B0  | inr Bₗ0≤k =
    ⊥-rec (¬m<m (≤<-trans Bₗ0≤k
                            (subst (k <_)
                                   (cong B (Fin-fst-≡ {i = fzero}
                                                       {j = inj-l-+ (suc m') n fzero}
                                                       refl))
                                   k<B0)))
  ... | inr B0≤k  | inl k<Bₗ0 =
    ⊥-rec (¬m<m (≤<-trans B0≤k
                            (subst (k <_)
                                   (sym (cong B (Fin-fst-≡ {i = fzero}
                                                            {j = inj-l-+ (suc m') n fzero}
                                                            refl)))
                                   k<Bₗ0)))
  ... | inr B0≤k  | inr Bₗ0≤k =
    -- Recursive case.
    -- LHS-reduced = C (fsuc (fst recF)) (snd recF) where
    --   recF = sumFinFwd (m' + n) (B ∘ fsuc) (k ∸ B fzero, klt-rec).
    -- RHS-reduced = (C ∘ inj-l-+ (suc m') n) (fsuc (fst recBₗ)) (snd recBₗ) where
    --   recBₗ = sumFinFwd m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc) (k ∸ Bₗ0, kltₗ-rec).
    --
    -- IH at m' relates them, modulo the family-reindexing
    -- (B ∘ inj-l-+ (suc m') n) ∘ fsuc ≡ (B ∘ fsuc) ∘ inj-l-+ m' n (by Fin-fst-≡ refl).
    let
      klt-rec  : k ∸ B fzero < sum (m' + n) (B ∘ fsuc)
      klt-rec  = ∸-<-lemma (B fzero) (sum (m' + n) (B ∘ fsuc)) k klt B0≤k
      kltₗ-rec : k ∸ (B ∘ inj-l-+ (suc m') n) fzero
               < sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)
      kltₗ-rec = ∸-<-lemma ((B ∘ inj-l-+ (suc m') n) fzero)
                            (sum m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)) k kltₗ Bₗ0≤k
      -- A propositional bridge between (k ∸ B fzero) and (k ∸ Bₗ0).
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
      -- IH application.
      IH : ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
             (k ∸ B fzero , klt-rec)
         ≡ ⅀Assoc-C' m' ((B ∘ fsuc) ∘ inj-l-+ m' n)
                          ((λ a' → C (fsuc a')) ∘ inj-l-+ m' n)
                          (k ∸ B fzero , kltₗ-rec')
      IH = ⅀Assoc-C'-add↑-on-l m' n (B ∘ fsuc) (λ a' → C (fsuc a'))
                                 (k ∸ B fzero) kltₗ-rec' klt-rec
      -- LHS-reduce: ⅀Assoc-C' (suc m' + n) B C (k, klt) ≡
      --   ⅀Assoc-C' (m'+n) (B∘fsuc) (C∘fsuc) (k ∸ B0, klt-rec).
      lhs-reduce : ⅀Assoc-C' (suc m' + n) B C (k , klt)
                 ≡ ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                              (k ∸ B fzero , klt-rec)
      lhs-reduce =
          cong (⅀Assoc-C' (suc m' + n) B C)
               (Fin-fst-≡ {i = (k , klt)}
                          {j = (B fzero + (k ∸ B fzero) , <-k+ {k = B fzero} klt-rec)}
                          (sym (∸-lemma B0≤k)))
        ∙ ⅀Assoc-C'-on-inr (m' + n) B C (k ∸ B fzero , klt-rec)
      -- RHS-reduce: ⅀Assoc-C' (suc m') Bₗ Cₗ (k, kltₗ) ≡
      --   ⅀Assoc-C' m' (Bₗ∘fsuc) (Cₗ∘fsuc) (k ∸ Bₗ0, kltₗ-rec).
      rhs-reduce : ⅀Assoc-C' m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)
                                  ((C ∘ inj-l-+ (suc m') n) ∘ fsuc)
                                  (k ∸ (B ∘ inj-l-+ (suc m') n) fzero , kltₗ-rec)
                 ≡ ⅀Assoc-C' (suc m') (B ∘ inj-l-+ (suc m') n)
                                       (C ∘ inj-l-+ (suc m') n) (k , kltₗ)
      rhs-reduce =
          sym (⅀Assoc-C'-on-inr m' (B ∘ inj-l-+ (suc m') n) (C ∘ inj-l-+ (suc m') n)
                                  (k ∸ (B ∘ inj-l-+ (suc m') n) fzero , kltₗ-rec))
        ∙ cong (⅀Assoc-C' (suc m') (B ∘ inj-l-+ (suc m') n)
                                    (C ∘ inj-l-+ (suc m') n))
               (Fin-fst-≡ {i = ( (B ∘ inj-l-+ (suc m') n) fzero
                               + (k ∸ (B ∘ inj-l-+ (suc m') n) fzero)
                               , <-k+ {k = (B ∘ inj-l-+ (suc m') n) fzero} kltₗ-rec)}
                          {j = (k , kltₗ)}
                          (∸-lemma Bₗ0≤k))
      -- Bridge IH's RHS to RHS-reduce's LHS.
      -- These differ in:
      --   1. The family: (B ∘ fsuc) ∘ inj-l-+ m' n vs (B ∘ inj-l-+ (suc m') n) ∘ fsuc.
      --   2. The C-family: similarly.
      --   3. The bound proof: kltₗ-rec' vs kltₗ-rec (propositional).
      --   4. The fst: (k ∸ B fzero) vs (k ∸ Bₗ0) (propositional).
      family-bridge :
          ⅀Assoc-C' m' ((B ∘ fsuc) ∘ inj-l-+ m' n)
                       ((λ a' → C (fsuc a')) ∘ inj-l-+ m' n)
                       (k ∸ B fzero , kltₗ-rec')
        ≡ ⅀Assoc-C' m' ((B ∘ inj-l-+ (suc m') n) ∘ fsuc)
                       ((C ∘ inj-l-+ (suc m') n) ∘ fsuc)
                       (k ∸ (B ∘ inj-l-+ (suc m') n) fzero , kltₗ-rec)
      family-bridge i =
        ⅀Assoc-C' m'
          (λ a → B (Fin-fst-≡ {i = fsuc (inj-l-+ m' n a)}
                               {j = inj-l-+ (suc m') n (fsuc a)} refl i))
          (λ a b → C (Fin-fst-≡ {i = fsuc (inj-l-+ m' n a)}
                                 {j = inj-l-+ (suc m') n (fsuc a)} refl i)
                       (Fin-fst-≡ {i = (fst b , _)} {j = (fst b , _)} refl i))
          (Fin-fst-≡ {i = (k ∸ B fzero , kltₗ-rec')}
                     {j = (k ∸ (B ∘ inj-l-+ (suc m') n) fzero , kltₗ-rec)}
                     ∸-bridge i)
    in lhs-reduce ∙ IH ∙ family-bridge ∙ rhs-reduce

  -- The "right half" analogue: ⅀Assoc-C' on inj-r-+ indices reduces
  -- to ⅀Assoc-C' at the right-side parameters.
  ⅀Assoc-C'-add↑-on-r :
    (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
    (k : ℕ)
    (kltᵣ : k < sum n (B ∘ inj-r-+ m n))
    (klt  : sum m (B ∘ inj-l-+ m n) + k < sum (m + n) B)
    → ⅀Assoc-C' (m + n) B C (sum m (B ∘ inj-l-+ m n) + k , klt)
    ≡ ⅀Assoc-C' n (B ∘ inj-r-+ m n) (C ∘ inj-r-+ m n) (k , kltᵣ)
  ⅀Assoc-C'-add↑-on-r zero    n B C k kltᵣ klt =
    -- m = 0: inj-l-+ is empty, inj-r-+ is identity (modulo Fin-fst-≡).
    -- LHS: ⅀Assoc-C' (0 + n) B C (0 + k, klt) = ⅀Assoc-C' n B C (k, _ ).
    -- RHS: ⅀Assoc-C' n (B ∘ inj-r-+ 0 n) (C ∘ inj-r-+ 0 n) (k, kltᵣ).
    -- Bridge: B ≡ B ∘ inj-r-+ 0 n by Fin-fst-≡ refl.
    λ i → ⅀Assoc-C' n (λ a → B (Fin-fst-≡ {i = a} {j = inj-r-+ zero n a} refl i))
                      (λ a b → C (Fin-fst-≡ {i = a} {j = inj-r-+ zero n a} refl i)
                                   (Fin-fst-≡ {i = (fst b , _)} {j = (fst b , _)} refl i))
                      (Fin-fst-≡ {i = (0 + k , klt)} {j = (k , kltᵣ)} refl i)
  ⅀Assoc-C'-add↑-on-r (suc m') n B C k kltᵣ klt =
    -- Recursive case: index sum (suc m') Bₗ + k = B fzero + sum m' (Bₗ ∘ fsuc) + k.
    -- We reduce LHS via ⅀Assoc-C'-on-inr to the (m' + n) level, then recurse.
    let
      Bₗ-fzero-eq : B fzero ≡ (B ∘ inj-l-+ (suc m') n) fzero
      Bₗ-fzero-eq = cong B (Fin-fst-≡ {i = fzero} {j = inj-l-+ (suc m') n fzero} refl)

      Bₗ-fsuc-eq : (a : Fin m')
                 → (B ∘ inj-l-+ (suc m') n) (fsuc a) ≡ B (fsuc (inj-l-+ m' n a))
      Bₗ-fsuc-eq a = cong B (Fin-fst-≡ {i = inj-l-+ (suc m') n (fsuc a)}
                                         {j = fsuc (inj-l-+ m' n a)} refl)

      Bᵣ-fsuc-eq : (a : Fin n)
                 → (B ∘ inj-r-+ (suc m') n) a ≡ B (fsuc (inj-r-+ m' n a))
      Bᵣ-fsuc-eq a = cong B (Fin-fst-≡ {i = inj-r-+ (suc m') n a}
                                         {j = fsuc (inj-r-+ m' n a)} refl)

      -- sum (suc m') Bₗ = Bₗ fzero + sum m' (Bₗ ∘ fsuc) definitionally.
      -- Bridge to (B fzero + sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n)) via the path:
      reix-sum-Bₗ : sum (suc m') (B ∘ inj-l-+ (suc m') n)
                  ≡ B fzero + sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n)
      reix-sum-Bₗ =
        cong₂ _+_ (sym Bₗ-fzero-eq)
                   (cong (sum m') (funExt (λ a → sym (Bₗ-fsuc-eq a))))

      -- Index reindex for the LHS.
      reix-Fin-fst : sum (suc m') (B ∘ inj-l-+ (suc m') n) + k
                   ≡ B fzero + (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k)
      reix-Fin-fst = cong (_+ k) reix-sum-Bₗ
                    ∙ sym (+-assoc (B fzero) (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n)) k)

      -- Bridge: full-klt is the bound on B fzero + (sum m' ... + k).
      full-klt : B fzero + (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k)
               < B fzero + sum (m' + n) (B ∘ fsuc)
      full-klt = subst (_< (B fzero + sum (m' + n) (B ∘ fsuc))) reix-Fin-fst klt

      -- Cancel B fzero on both sides via <-k+-cancel.
      klt-inner : sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k < sum (m' + n) (B ∘ fsuc)
      klt-inner = <-k+-cancel {k = B fzero} full-klt

      kltᵣ' : k < sum n ((B ∘ fsuc) ∘ inj-r-+ m' n)
      kltᵣ' = subst (k <_)
                     (sym (cong (sum n) (funExt (λ a → Bᵣ-fsuc-eq a))))
                     kltᵣ

      IH : ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
             (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k , klt-inner)
         ≡ ⅀Assoc-C' n ((B ∘ fsuc) ∘ inj-r-+ m' n)
                          ((λ a' → C (fsuc a')) ∘ inj-r-+ m' n) (k , kltᵣ')
      IH = ⅀Assoc-C'-add↑-on-r m' n (B ∘ fsuc) (λ a' → C (fsuc a')) k kltᵣ' klt-inner

      -- LHS reduction step.
      lhs-step : ⅀Assoc-C' (suc m' + n) B C
                   (sum (suc m') (B ∘ inj-l-+ (suc m') n) + k , klt)
               ≡ ⅀Assoc-C' (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                              (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k , klt-inner)
      lhs-step = cong (⅀Assoc-C' (suc m' + n) B C) (Fin-fst-≡ reix-Fin-fst)
                ∙ ⅀Assoc-C'-on-inr (m' + n) B C
                    (sum m' ((B ∘ fsuc) ∘ inj-l-+ m' n) + k , klt-inner)

      -- RHS bridge: from IH's RHS to the goal's RHS.
      rhs-bridge : ⅀Assoc-C' n ((B ∘ fsuc) ∘ inj-r-+ m' n)
                                  ((λ a' → C (fsuc a')) ∘ inj-r-+ m' n) (k , kltᵣ')
                 ≡ ⅀Assoc-C' n (B ∘ inj-r-+ (suc m') n) (C ∘ inj-r-+ (suc m') n)
                                  (k , kltᵣ)
      rhs-bridge i =
        ⅀Assoc-C' n
          (λ a → B (Fin-fst-≡ {i = fsuc (inj-r-+ m' n a)}
                               {j = inj-r-+ (suc m') n a} refl i))
          (λ a b → C (Fin-fst-≡ {i = fsuc (inj-r-+ m' n a)}
                                  {j = inj-r-+ (suc m') n a} refl i)
                       (Fin-fst-≡ {i = (fst b , _)} {j = (fst b , _)} refl i))
          (Fin-fst-≡ {i = (k , kltᵣ')} {j = (k , kltᵣ)} refl i)
    in lhs-step ∙ IH ∙ rhs-bridge
-}

opaque
  -- Transporting sum-prefix-ℕ along paths on both the bound and the function:
  -- this is just `λ i → sum-prefix-ℕ (p i) (q i) k` by joint continuity.
  sum-prefix-ℕ-PathP : {X Y : ℕ} (p : X ≡ Y) {f : Fin X → ℕ} {g : Fin Y → ℕ}
                     → PathP (λ i → Fin (p i) → ℕ) f g
                     → (k : ℕ)
                     → sum-prefix-ℕ X f k ≡ sum-prefix-ℕ Y g k
  sum-prefix-ℕ-PathP p q k i = sum-prefix-ℕ (p i) (q i) k

  fubini : (A : ℕ) (B : Fin A → ℕ) (C : (a : Fin A) → Fin (B a) → ℕ)
         → (a : Fin A) (b : Fin (B a))
         → sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C)
                        (sum-prefix-ℕ A B (fst a) + fst b)
         ≡ sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a)
         + sum-prefix-ℕ (B a) (C a) (fst b)
  fubini zero    B C (_     , p) b = ⊥-rec (¬-<-zero p)
  fubini (suc A') B C (zero  , p) b =
    -- LHS reduces (since sum-prefix-ℕ (suc A') B 0 = 0) to
    --   sum-prefix-ℕ (B fzero + sum A' (B ∘ fsuc)) (⅀Assoc-C' (suc A') B C) (fst b)
    -- with `b : Fin (B (zero, p))`, hence fst b < B (zero, p) ≡ B fzero.
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
    -- LHS = sum-prefix-ℕ (B fzero + sum A' (B ∘ fsuc)) (⅀Assoc-C') (B fzero + sum-prefix-ℕ A' (B ∘ fsuc) k + fst b)
    -- Reassociate index, then apply sum-prefix-ℕ-r.
      cong (sum-prefix-ℕ (B fzero + sum A' (B ∘ fsuc)) (⅀Assoc-C' (suc A') B C))
           (sym (+-assoc (B fzero) (sum-prefix-ℕ A' (B ∘ fsuc) k) (fst b)))
    ∙ sum-prefix-ℕ-r (B fzero) (sum A' (B ∘ fsuc))
                      (⅀Assoc-C' (suc A') B C)
                      (sum-prefix-ℕ A' (B ∘ fsuc) k + fst b)
                      bound-ok
    -- The first summand simplifies via ⅀Assoc-C'-on-inl + sum-cong.
    -- The second simplifies via ⅀Assoc-C'-on-inr + sum-prefix-ℕ-cong, then IH.
    ∙ cong₂ _+_
          (sum-cong (B fzero) (⅀Assoc-C'-on-inl A' B C))
          ( sum-prefix-ℕ-cong (sum A' (B ∘ fsuc))
                                (⅀Assoc-C'-on-inr A' B C)
                                (sum-prefix-ℕ A' (B ∘ fsuc) k + fst b)
          ∙ fubini A' (B ∘ fsuc) (λ a' → C (fsuc a')) (k , pred-≤-pred p) b' )
    -- Reassociate and bridge to RHS.
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

      -- b bridged from Fin (B (suc k, p)) to Fin ((B ∘ fsuc) (k, pred-≤-pred p)).
      b' : Fin ((B ∘ fsuc) (k , pred-≤-pred p))
      b' = subst (λ x → Fin (B x)) fsuc-eq b

      -- fst b' = fst b (transport preserves fst on Fin).
      fst-b'≡fst-b : fst b' ≡ fst b
      fst-b'≡fst-b = fst-subst-Fin (cong B fsuc-eq) b
        where
          fst-subst-Fin : {a b : ℕ} (q : a ≡ b) (x : Fin a)
                        → fst (subst Fin q x) ≡ fst x
          fst-subst-Fin {a} = J (λ b q → (x : Fin a) → fst (subst Fin q x) ≡ fst x)
                                (λ x → cong fst (substRefl {B = Fin} x))

      -- The bound for sum-prefix-ℕ-r: sum-prefix-ℕ A' (B ∘ fsuc) k + fst b ≤ sum A' (B ∘ fsuc).
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

------------------------------------------------------------------------
-- Inverse fst-preservation, via the trace through the 5 composed steps.
------------------------------------------------------------------------

-- Definitional check: invEq of ⅀Assoc≃ traces through the 5 reverse steps
-- to land on `sumFinBwd A (λ a → sum (B a) (C a)) (a , sumFinBwd (B a) (C a) (b , c))`,
-- where (ab, c) = sumFinFwd (sum A B) ⅀Assoc-C' k and (a, b) = sumFinFwd A B ab.
-- fst is then literally `sum-prefix A (λ a → sum (B a) (C a)) a + (sum-prefix (B a) (C a) b + fst c)`.
private
  module _ (A : ℕ) (B : Fin A → ℕ) (C : (a : Fin A) → Fin (B a) → ℕ)
           (k : Fin (sum (sum A B) (⅀Assoc-C' A B C))) where
    abc = sumFinFwd (sum A B) (⅀Assoc-C' A B C) k
    ab  = fst abc
    c   = snd abc
    ab' = sumFinFwd A B ab
    a   = fst ab'
    b   = snd ab'

    -- Sanity: the fst of the invEq result is exactly the expected expression.
    _ : fst (invEq (⅀Assoc≃ A B C) k)
      ≡ sum-prefix A (λ a' → sum (B a') (C a')) a
      + (sum-prefix (B a) (C a) b + fst c)
    _ = refl

opaque
  ⅀Assoc-preserves-fst-INV : (A : ℕ) (B : Fin A → ℕ)
                             (C : (a : Fin A) → Fin (B a) → ℕ)
                           → (k : Fin (sum (sum A B) (⅀Assoc-C' A B C)))
                           → fst (invEq (⅀Assoc≃ A B C) k) ≡ fst k
  ⅀Assoc-preserves-fst-INV A B C k =
    -- Definitionally (sanity check above):
    --   fst (invEq ⅀Assoc≃ k) = sum-prefix A (..) a + (sum-prefix (B a) (C a) b + fst c).
    -- We rebracket and use fubini to fold this back to
    --   sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix A B a + fst b) + fst c.
    -- Then `sum-prefix A B a + fst b = fst (sumFinBwd A B (a, b))` definitionally,
    -- and `sumFinBwd A B (a, b)` is propositionally `ab` via sumFinBwd-Fwd applied
    -- to (a, b) = sumFinFwd A B ab. Finally, sumFinBwd-Fwd of k on the outer level
    -- bridges fst k.
    let abc = sumFinFwd (sum A B) (⅀Assoc-C' A B C) k
        ab  = fst abc
        c   = snd abc
        ab' = sumFinFwd A B ab
        a   = fst ab'
        b   = snd ab'
        -- Step 1: bridge both sum-prefix to sum-prefix-ℕ
        step1 : sum-prefix A (λ a' → sum (B a') (C a')) a + (sum-prefix (B a) (C a) b + fst c)
              ≡ sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + (sum-prefix-ℕ (B a) (C a) (fst b) + fst c)
        step1 = cong₂ _+_ (sum-prefix-≡ A _ a)
                            (cong (_+ fst c) (sum-prefix-≡ (B a) (C a) b))
        -- Step 2: reassociate to (X + Y) + Z
        step2 : sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + (sum-prefix-ℕ (B a) (C a) (fst b) + fst c)
              ≡ sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + sum-prefix-ℕ (B a) (C a) (fst b) + fst c
        step2 = +-assoc (sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a))
                        (sum-prefix-ℕ (B a) (C a) (fst b))
                        (fst c)
        -- Step 3: apply sym (fubini) — note fubini's RHS matches step2's RHS
        step3 : sum-prefix-ℕ A (λ a' → sum (B a') (C a')) (fst a) + sum-prefix-ℕ (B a) (C a) (fst b) + fst c
              ≡ sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix-ℕ A B (fst a) + fst b) + fst c
        step3 = cong (_+ fst c) (sym (fubini A B C a b))
        -- Step 4: bridge sum-prefix-ℕ A B (fst a) back to sum-prefix A B a
        step4 : sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix-ℕ A B (fst a) + fst b) + fst c
              ≡ sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix A B a + fst b) + fst c
        step4 = cong (λ x → sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (x + fst b) + fst c)
                     (sym (sum-prefix-≡ A B a))
        -- Step 5: sum-prefix A B a + fst b = fst (sumFinBwd A B (a, b)) definitionally;
        --         and sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (fst x) is the "fst-on-Fin"
        --         interpretation. Bridge sum-prefix-ℕ to sum-prefix:
        step5 : sum-prefix-ℕ (sum A B) (⅀Assoc-C' A B C) (sum-prefix A B a + fst b) + fst c
              ≡ sum-prefix (sum A B) (⅀Assoc-C' A B C) (sumFinBwd A B (a , b)) + fst c
        step5 = cong (_+ fst c) (sym (sum-prefix-≡ (sum A B) (⅀Assoc-C' A B C) (sumFinBwd A B (a , b))))
        -- Step 6: sumFinBwd-Fwd A B ab — applied to (a, b) = sumFinFwd A B ab.
        step6 : sum-prefix (sum A B) (⅀Assoc-C' A B C) (sumFinBwd A B (a , b)) + fst c
              ≡ sum-prefix (sum A B) (⅀Assoc-C' A B C) ab + fst c
        step6 = cong (λ x → sum-prefix (sum A B) (⅀Assoc-C' A B C) x + fst c)
                     (sumFinBwd-Fwd A B ab)
        -- Step 7: by definition of sumFinBwd, this equals fst (sumFinBwd (sum A B) (⅀Assoc-C' A B C) (ab, c)).
        --         And sumFinBwd-Fwd on the outer level gives this = fst k.
        step7 : sum-prefix (sum A B) (⅀Assoc-C' A B C) ab + fst c
              ≡ fst k
        step7 = cong fst (sumFinBwd-Fwd (sum A B) (⅀Assoc-C' A B C) k)
    in step1 ∙ step2 ∙ step3 ∙ step4 ∙ step5 ∙ step6 ∙ step7

  -- Forward direction is derived via `retEq`.
  ⅀Assoc-preserves-fst : (A : ℕ) (B : Fin A → ℕ)
                         (C : (a : Fin A) → Fin (B a) → ℕ)
                         (k : Fin (sum A (λ a → sum (B a) (C a))))
                       → fst (equivFun (⅀Assoc≃ A B C) k) ≡ fst k
  ⅀Assoc-preserves-fst A B C k =
      sym (⅀Assoc-preserves-fst-INV A B C (equivFun (⅀Assoc≃ A B C) k))
    ∙ cong fst (retEq (⅀Assoc≃ A B C) k)

-- Assembled coherence record.
𝓝-coh : UniverseCoh 𝓝-base
UniverseCoh.⟦⅀Idl⟧   𝓝-coh A     = coh-from-fst (⅀Idl≃ A)         (+-zero A)   (⅀Idl-preserves-fst A)
UniverseCoh.⟦⅀Idr⟧   𝓝-coh A     = coh-from-fst (⅀Idr≃ A)         (sum-idr A) (⅀Idr-preserves-fst A)
UniverseCoh.⟦⅀Assoc⟧ 𝓝-coh A B C = coh-from-fst (⅀Assoc≃ A B C)   (NatInj (⅀Assoc≃ A B C))
                                                (⅀Assoc-preserves-fst A B C)

-- The 𝓝 universe of totally-ordered finite sets.
𝓝 : Universe ℓ-zero ℓ-zero
Universe.base 𝓝 = 𝓝-base
Universe.coh  𝓝 = 𝓝-coh
