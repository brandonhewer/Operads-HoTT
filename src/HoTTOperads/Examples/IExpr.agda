{-# OPTIONS --cubical #-}
module HoTTOperads.Examples.IExpr where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (substComposite)
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties using (+-zero ; +-assoc ; +-comm)
open import Cubical.Data.Nat.Order using (_<_ ; _≤_ ; <-k+ ; ¬m<m ; ≤<-trans ; ¬-<-zero
                                          ; pred-≤-pred ; zero-≤ ; suc-≤-suc ; isProp≤
                                          ; ¬m+n<m ; <-k+-cancel ; ≤-trans ; ≤-reflexive
                                          ; ≤SumLeft ; <-weaken ; ≤-+k ; ≤-k+)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Fin.Properties using (Fin-fst-≡ ; o<m→o<m+n ; _≤?_ ; ∸-<-lemma
                                              ; m+n∸n=m ; ∸-lemma ; isSetFin)
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (Σ≡Prop ; ΣPathP)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Instances.Nat using (𝓝 ; sum ; ⅀Assoc-C'-on-inl ; ⅀Assoc-C'-on-inr)
open import HoTTOperads.Prelude.Nat using (transport-Fin-fst ; sumFinFwd ; sum-prefix-bound)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Specialised.NonSymm using (NonSymmOperad)

-- A simple expression language as a target for our operad.
data Expr : Type where
  val : ℕ → Expr
  add : Expr → Expr → Expr

-- The abstract operations as an inductive family indexed by arity.
data IExpr : ℕ → Type where
  id↑  : IExpr 1
  val↑ : ℕ → IExpr 0
  add↑ : ∀ {m n} → IExpr m → IExpr n → IExpr (m + n)

------------------------------------------------------------------------
-- Unindexed underlying tree, used as the target of a retract to prove
-- isSet (IExpr n). Tree is a free inductive type, so isSet Tree is the
-- standard encode-decode argument.  Mirrors SymExpr.Tree but with ℕ as
-- the shape index instead of FinSet.
------------------------------------------------------------------------
data Tree : Type where
  Tid  : Tree
  Tval : ℕ → Tree
  Tadd : Tree → Tree → Tree

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

opaque
  isSetTree : isSet Tree
  isSetTree s t =
    isOfHLevelRetract 1
      (TreePath.encode s t)
      (TreePath.decode s t)
      (TreePath.decodeEncode s t)
      (TreePath.isOfHLevelCover 0 s t)

------------------------------------------------------------------------
-- Shape and forgetful map between Tree and IExpr.
------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- Pushing subst through add↑, mirroring SymExpr.subst-add↑.  Used by the
-- g∘f round-trip below as well as IExpr-idr's add↑ case downstream.
------------------------------------------------------------------------
opaque
  subst-add↑ : ∀ {m m' n n'}
               (p₁ : m ≡ m') (p₂ : n ≡ n')
               (e₁ : IExpr m) (e₂ : IExpr n)
             → subst IExpr (cong₂ _+_ p₁ p₂) (add↑ e₁ e₂)
             ≡ add↑ (subst IExpr p₁ e₁) (subst IExpr p₂ e₂)
  subst-add↑ p₁ p₂ e₁ e₂ =
    fromPathP (λ i → add↑ (subst-filler IExpr p₁ e₁ i)
                          (subst-filler IExpr p₂ e₂ i))

------------------------------------------------------------------------
-- The retract pair (f, g) and the round-trip g ∘ f ≡ id.  Mirrors
-- SymExpr.f / SymExpr.g / SymExpr.g∘f at the ℕ-indexed level.  Kept
-- transparent: opaque on g∘f breaks substRefl family inference.
------------------------------------------------------------------------
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

------------------------------------------------------------------------
-- isSetIExpr, by retract to IExprTreeΣ.  IExprTreeΣ n is a Σ of a set
-- (Tree) and a set (ℕ-paths), so a set itself.
------------------------------------------------------------------------
opaque
  isSetIExprTreeΣ : (n : ℕ) → isSet (IExprTreeΣ n)
  isSetIExprTreeΣ n = isSetΣ isSetTree (λ t → isProp→isSet (isSetℕ (shape t) n))

  isSetIExpr : (n : ℕ) → isSet (IExpr n)
  isSetIExpr n = isOfHLevelRetract 2 f g g∘f (isSetIExprTreeΣ n)

------------------------------------------------------------------------
-- Private arithmetic helpers used to define IExpr-comp on the add↑ case.
-- The injections compute; the propositional sum-split lemma is wrapped
-- in opaque so Agda's normaliser treats it as a black box outside.
------------------------------------------------------------------------
private
  injL : (m n : ℕ) → Fin m → Fin (m + n)
  injL m n (k , p) = k , o<m→o<m+n m n k p

  injR : (m n : ℕ) → Fin n → Fin (m + n)
  injR m n (k , p) = m + k , <-k+ p

  opaque
    -- The sum over Fin (m + n) splits into a sum over the Fin m prefix
    -- and a sum over the Fin n suffix. Direct induction on m; avoids
    -- depending on sumFinEquiv.
    sum-split : (m n : ℕ) (B : Fin (m + n) → ℕ)
              → sum (m + n) B ≡ sum m (B ∘ injL m n) + sum n (B ∘ injR m n)
    sum-split zero    n B =
      cong (sum n) (funExt λ kp → cong B (Fin-fst-≡ refl))
    sum-split (suc m) n B =
        B fzero + sum (m + n) (B ∘ fsuc)
          ≡⟨ cong (B fzero +_) (sum-split m n (B ∘ fsuc)) ⟩
        B fzero + (sum m (B ∘ fsuc ∘ injL m n) + sum n (B ∘ fsuc ∘ injR m n))
          ≡⟨ +-assoc (B fzero) _ _ ⟩
        (B fzero + sum m (B ∘ fsuc ∘ injL m n)) + sum n (B ∘ fsuc ∘ injR m n)
          ≡⟨ cong₂ _+_ left-eq right-eq ⟩
        sum (suc m) (B ∘ injL (suc m) n) + sum n (B ∘ injR (suc m) n) ∎
      where
        left-eq : B fzero + sum m (B ∘ fsuc ∘ injL m n)
                ≡ B (injL (suc m) n fzero) + sum m (B ∘ injL (suc m) n ∘ fsuc)
        left-eq = cong₂ _+_ (cong B (Fin-fst-≡ refl))
                           (cong (sum m) (funExt λ kp → cong B (Fin-fst-≡ refl)))
        right-eq : sum n (B ∘ fsuc ∘ injR m n) ≡ sum n (B ∘ injR (suc m) n)
        right-eq = cong (sum n) (funExt λ kp → cong B (Fin-fst-≡ refl))

------------------------------------------------------------------------
-- IExpr-comp: the n-ary operadic composition, defined by induction on the
-- IExpr argument (BasicIdea.tex §1).
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
    (add↑ (IExpr-comp m (B ∘ injL m n) e₁ (es ∘ injL m n))
          (IExpr-comp n (B ∘ injR m n) e₂ (es ∘ injR m n)))

private
  opaque
    -- Pure congruence of IExpr-comp under heterogeneous paths in all four
    -- arguments. The body is just λ i → IExpr-comp (p i) (B-path i) (e-path i)
    -- (es-path i); the caller supplies the index-path, the family-path, the
    -- IExpr-path, and the dependent-function-path.
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

    -- Alignment of ⅀Assoc-C' 𝓝 1 B C with C fzero under +-zero (B fzero)
    -- reindexing.  Proof by manual case-split on `_≤?_` inside sumFinFwd 1 B;
    -- the inr branch is impossible.  Agda's `with` propagates the match
    -- to the `with` inside sumFinFwd, so the LHS of each clause reduces.
    ⅀Assoc-C'-id↑-eq :
      (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
      (a : Fin (B fzero + 0))
      → Universe.⅀Assoc-C' 𝓝 1 B C a
      ≡ C fzero (fst a , subst ((fst a) <_) (+-zero (B fzero)) (snd a))
    ⅀Assoc-C'-id↑-eq B C (k , prf) with k ≤? B fzero
    ... | inl k<m = cong (C fzero) (Fin-fst-≡ refl)
    ... | inr m≤k =
      ⊥-rec (¬m<m (≤<-trans m≤k (subst (k <_) (+-zero (B fzero)) prf)))

    -- Heterogeneous alignment of the abstract `kss-at-⅀Assoc-C'` function
    -- with the concrete kss fzero through the same +-zero (B fzero)
    -- reindexing, as a PathP over IExpr applied to ⅀Assoc-C'-id↑-eq.
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
      ⊥-rec (¬m<m (≤<-trans m≤k (subst (k <_) (+-zero (B fzero)) prf)))

------------------------------------------------------------------------
-- Left identity: comp 1 (λ _ → A) id↑ (λ _ → k) reduces definitionally to
-- subst IExpr (sym (+-zero A)) k. The PathP is obtained by reversing the
-- subst-filler and swapping the index path via isSetℕ.
------------------------------------------------------------------------
opaque
  IExpr-idl : (A : ℕ) (k : IExpr A)
            → PathP (λ i → IExpr (Universe.Inj 𝓝 (Universe.⅀Idl≃ 𝓝 A) i))
                    (IExpr-comp 1 (λ _ → A) id↑ (λ _ → k)) k
  IExpr-idl A k =
    subst (λ p → PathP (λ i → IExpr (p i))
                       (subst IExpr (sym (+-zero A)) k) k)
          (isSetℕ _ _ (+-zero A) (Universe.Inj 𝓝 (Universe.⅀Idl≃ 𝓝 A)))
          (symP (subst-filler IExpr (sym (+-zero A)) k))

------------------------------------------------------------------------
-- Right identity. By induction on k, three cases. For each constructor
-- we build a PathP via subst-filler over a convenient ℕ-path, then swap
-- the index path for Inj 𝓝 (⅀Idr≃ 𝓝 A) via isSetℕ.
------------------------------------------------------------------------
opaque
  IExpr-idr : (A : ℕ) (k : IExpr A)
            → PathP (λ i → IExpr (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 A) i))
                    (IExpr-comp A (λ _ → 1) k (λ _ → id↑)) k
  IExpr-idr .1 id↑ =
    subst (λ p → PathP (λ i → IExpr (p i))
                       (subst IExpr (sym (+-zero 1)) id↑) id↑)
          (isSetℕ _ _ (+-zero 1) (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 1)))
          (symP (subst-filler IExpr (sym (+-zero 1)) id↑))
  IExpr-idr .0 (val↑ n) =
    subst (λ p → PathP (λ i → IExpr (p i)) (val↑ n) (val↑ n))
          (isSetℕ _ _ refl (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 0)))
          refl
  IExpr-idr .(m + n) (add↑ {m} {n} e₁ e₂) =
    subst (λ p → PathP (λ i → IExpr (p i)) lhs (add↑ e₁ e₂))
          (isSetℕ _ _ _ (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 (m + n))))
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

------------------------------------------------------------------------
-- Associativity. Discharged by induction on the IExpr argument:
--   val↑ (A = 0): definitional, refl + isSetℕ swap.
--   id↑  (A = 1): IExpr-assoc-id↑ helper (lines below).
--   add↑ (A = m + n): IExpr-assoc-add↑ via (m+n)-level Fubini lemmas
--                     (sumFinFwd-add↑-on-l/r) and recursion on e₁/e₂.
------------------------------------------------------------------------
------------------------------------------------------------------------
-- (m+n)-level Fubini lemmas, generalised from the suc-level versions in
-- Universe/Instances/Nat by induction on m. These are needed to discharge
-- the add↑ case of IExpr-assoc.
------------------------------------------------------------------------

private
  opaque
    unfolding sum-split

    -- The left-half (m+n) Fubini: ⅀Assoc-C' at a "left-half" index reduces
    -- to ⅀Assoc-C' at the m-level via the inj-l-+ reindexing.
    -- Takes both bound proofs as explicit args (they're propositionally
    -- but not definitionally equal).
    ⅀Assoc-C'-add↑-on-l :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
      (k : ℕ)
      (kltₗ : k < sum m (B ∘ injL m n))
      (klt  : k < sum (m + n) B)
      → Universe.⅀Assoc-C' 𝓝 (m + n) B C (k , klt)
      ≡ Universe.⅀Assoc-C' 𝓝 m (B ∘ injL m n) (C ∘ injL m n) (k , kltₗ)
    ⅀Assoc-C'-add↑-on-l zero    n B C k kltₗ klt = ⊥-rec (¬-<-zero kltₗ)
    ⅀Assoc-C'-add↑-on-l (suc m') n B C k kltₗ klt
      with k ≤? B fzero | k ≤? (B ∘ injL (suc m') n) fzero
    ... | inl k<B0 | inl k<Bₗ0 =
      -- Both reduce: LHS = C fzero (k, k<B0), RHS = C (injL (suc m') n fzero) (k, k<Bₗ0).
      let
        fz-path : (fzero {k = m' + n}) ≡ injL (suc m') n fzero
        fz-path = Fin-fst-≡ refl
        sn-path : PathP (λ j → Fin (B (fz-path j))) (k , k<B0) (k , k<Bₗ0)
        sn-path = ΣPathP (refl , isProp→PathP (λ _ → isProp≤) k<B0 k<Bₗ0)
      in λ i → C (fz-path i) (sn-path i)
    ... | inl k<B0 | inr Bₗ0≤k =
      ⊥-rec (¬m<m (≤<-trans Bₗ0≤k
                              (subst (k <_)
                                     (cong B (Fin-fst-≡ {i = fzero}
                                                         {j = injL (suc m') n fzero}
                                                         refl))
                                     k<B0)))
    ... | inr B0≤k | inl k<Bₗ0 =
      ⊥-rec (¬m<m (≤<-trans B0≤k
                              (subst (k <_)
                                     (sym (cong B (Fin-fst-≡ {i = fzero}
                                                              {j = injL (suc m') n fzero}
                                                              refl)))
                                     k<Bₗ0)))
    ... | inr B0≤k | inr Bₗ0≤k =
      -- Recursive case. In the inr/inr branch, both LHS and RHS reduce
      -- definitionally to (m'+n) and m'-level ⅀Assoc-C' applications.
      -- We just need to bridge via IH + family-bridge.
      let
        ∸-bridge : k ∸ B fzero ≡ k ∸ (B ∘ injL (suc m') n) fzero
        ∸-bridge = cong (k ∸_) (cong B (Fin-fst-≡ {i = fzero}
                                                    {j = injL (suc m') n fzero} refl))

        klt-rec : k ∸ B fzero < sum (m' + n) (B ∘ fsuc)
        klt-rec = ∸-<-lemma (B fzero) (sum (m' + n) (B ∘ fsuc)) k klt B0≤k

        kltₗ-rec : k ∸ (B ∘ injL (suc m') n) fzero
                 < sum m' ((B ∘ injL (suc m') n) ∘ fsuc)
        kltₗ-rec = ∸-<-lemma ((B ∘ injL (suc m') n) fzero)
                              (sum m' ((B ∘ injL (suc m') n) ∘ fsuc)) k kltₗ Bₗ0≤k

        kltₗ-rec' : k ∸ B fzero < sum m' ((B ∘ fsuc) ∘ injL m' n)
        kltₗ-rec' = subst (k ∸ B fzero <_)
                           (cong (sum m')
                                 (funExt λ a → cong B (Fin-fst-≡
                                   {i = injL (suc m') n (fsuc a)}
                                   {j = fsuc (injL m' n a)} refl)))
                           (subst (_< sum m' ((B ∘ injL (suc m') n) ∘ fsuc))
                                  (sym ∸-bridge)
                                  kltₗ-rec)

        IH : Universe.⅀Assoc-C' 𝓝 (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                                  (k ∸ B fzero , klt-rec)
           ≡ Universe.⅀Assoc-C' 𝓝 m' ((B ∘ fsuc) ∘ injL m' n)
                                       ((λ a' → C (fsuc a')) ∘ injL m' n)
                                       (k ∸ B fzero , kltₗ-rec')
        IH = ⅀Assoc-C'-add↑-on-l m' n (B ∘ fsuc) (λ a' → C (fsuc a'))
                                   (k ∸ B fzero) kltₗ-rec' klt-rec

        -- The family-path used at each i.
        B-fam-path : (a : Fin m')
                   → (B ∘ fsuc) ((injL m' n) a) ≡ (B ∘ injL (suc m') n) (fsuc a)
        B-fam-path a = cong B (Fin-fst-≡ {i = fsuc (injL m' n a)}
                                            {j = injL (suc m') n (fsuc a)} refl)
        -- The Fin element bridge.
        Σ-elem : PathP (λ i → Fin (sum m' (λ a → B-fam-path a i)))
                       (k ∸ B fzero , kltₗ-rec')
                       (k ∸ (B ∘ injL (suc m') n) fzero , kltₗ-rec)
        Σ-elem = ΣPathP {A = λ _ → ℕ}
                         {B = λ i k → k < sum m' (λ a → B-fam-path a i)}
                         (∸-bridge , isProp→PathP (λ _ → isProp≤) kltₗ-rec' kltₗ-rec)
        family-bridge :
            Universe.⅀Assoc-C' 𝓝 m' ((B ∘ fsuc) ∘ injL m' n)
                                       ((λ a' → C (fsuc a')) ∘ injL m' n)
                                       (k ∸ B fzero , kltₗ-rec')
          ≡ Universe.⅀Assoc-C' 𝓝 m' ((B ∘ injL (suc m') n) ∘ fsuc)
                                       ((C ∘ injL (suc m') n) ∘ fsuc)
                                       (k ∸ (B ∘ injL (suc m') n) fzero , kltₗ-rec)
        family-bridge i =
          Universe.⅀Assoc-C' 𝓝 m'
            (λ a → B-fam-path a i)
            (λ a b → C (Fin-fst-≡ {i = fsuc (injL m' n a)}
                                    {j = injL (suc m') n (fsuc a)} refl i)
                         b)
            (Σ-elem i)
      in IH ∙ family-bridge

  opaque
    unfolding sum-split

    -- The right-half (m+n) Fubini: ⅀Assoc-C' at sum m Bₗ + k reduces to ⅀Assoc-C' n
    -- via injR m n reindexing.
    ⅀Assoc-C'-add↑-on-r :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
      (k : ℕ)
      (kltᵣ : k < sum n (B ∘ injR m n))
      (klt  : sum m (B ∘ injL m n) + k < sum (m + n) B)
      → Universe.⅀Assoc-C' 𝓝 (m + n) B C (sum m (B ∘ injL m n) + k , klt)
      ≡ Universe.⅀Assoc-C' 𝓝 n (B ∘ injR m n) (C ∘ injR m n) (k , kltᵣ)
    ⅀Assoc-C'-add↑-on-r zero    n B C k kltᵣ klt =
      -- LHS index reduces: sum 0 _ + k = 0 + k = k.
      -- So we're bridging ⅀Assoc-C' n B C (k, klt) ≡ ⅀Assoc-C' n (B ∘ injR 0 n) (C ∘ injR 0 n) (k, kltᵣ).
      -- Use a family-bridge via cong on B ∘ injR 0 n ≡ B (per element via Fin-fst-≡ refl).
      let
        B-fam-path : (a : Fin n) → B a ≡ (B ∘ injR zero n) a
        B-fam-path a = cong B (Fin-fst-≡ {i = a} {j = injR zero n a} refl)
        Σ-elem : PathP (λ i → Fin (sum n (λ a → B-fam-path a i)))
                       (k , klt) (k , kltᵣ)
        Σ-elem = ΣPathP {A = λ _ → ℕ}
                         {B = λ i k' → k' < sum n (λ a → B-fam-path a i)}
                         (refl , isProp→PathP (λ _ → isProp≤) klt kltᵣ)
      in λ i → Universe.⅀Assoc-C' 𝓝 n (λ a → B-fam-path a i)
                                       (λ a b → C (Fin-fst-≡ {i = a} {j = injR zero n a} refl i) b)
                                       (Σ-elem i)
    ⅀Assoc-C'-add↑-on-r (suc m') n B C k kltᵣ klt =
      -- LHS index: sum (suc m') (B ∘ injL (suc m') n) + k = (B ∘ injL ...) fzero + sum m' (...) + k.
      -- We bridge to (B fzero + (something + k), _) and apply suc-level on-inr at the top.
      let
        Bₗ-fzero-eq : B fzero ≡ (B ∘ injL (suc m') n) fzero
        Bₗ-fzero-eq = cong B (Fin-fst-≡ {i = fzero} {j = injL (suc m') n fzero} refl)

        -- Bridge index: (Bₗ fzero + sum m' (Bₗ ∘ fsuc)) + k = sum (suc m') Bₗ + k.
        index-bridge : sum (suc m') (B ∘ injL (suc m') n) + k
                     ≡ B fzero + (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k)
        index-bridge = cong (_+ k) (cong (_+ sum m' ((B ∘ injL (suc m') n) ∘ fsuc))
                                          (sym Bₗ-fzero-eq))
                      ∙ sym (+-assoc (B fzero) (sum m' ((B ∘ injL (suc m') n) ∘ fsuc)) k)

        -- Bound proof for the inner recursion: sum m' (Bₗ ∘ fsuc) + k < sum (m' + n) (B ∘ fsuc).
        full-klt : B fzero + (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k)
                 < B fzero + sum (m' + n) (B ∘ fsuc)
        full-klt = subst (_< B fzero + sum (m' + n) (B ∘ fsuc)) index-bridge klt

        klt-inner : sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k < sum (m' + n) (B ∘ fsuc)
        klt-inner = <-k+-cancel {k = B fzero} full-klt

        -- Bridge the inner bound to the m'-level form expected by the IH.
        sum-prefix-fam-path : (a : Fin m')
                            → (B ∘ injL (suc m') n) (fsuc a) ≡ (B ∘ fsuc) (injL m' n a)
        sum-prefix-fam-path a = cong B (Fin-fst-≡ {i = injL (suc m') n (fsuc a)}
                                                    {j = fsuc (injL m' n a)} refl)

        klt-inner' : sum m' ((B ∘ fsuc) ∘ injL m' n) + k < sum (m' + n) (B ∘ fsuc)
        klt-inner' = subst (_< sum (m' + n) (B ∘ fsuc))
                            (cong (_+ k) (cong (sum m') (funExt sum-prefix-fam-path)))
                            klt-inner

        -- Bridge the right-side family.
        Bᵣ-fam-path : (a : Fin n)
                    → (B ∘ injR (suc m') n) a ≡ (B ∘ fsuc) (injR m' n a)
        Bᵣ-fam-path a = cong B (Fin-fst-≡ {i = injR (suc m') n a}
                                            {j = fsuc (injR m' n a)} refl)

        kltᵣ' : k < sum n ((B ∘ fsuc) ∘ injR m' n)
        kltᵣ' = subst (k <_) (cong (sum n) (funExt Bᵣ-fam-path)) kltᵣ

        IH : Universe.⅀Assoc-C' 𝓝 (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
               (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner')
           ≡ Universe.⅀Assoc-C' 𝓝 n ((B ∘ fsuc) ∘ injR m' n)
                                       ((λ a' → C (fsuc a')) ∘ injR m' n) (k , kltᵣ')
        IH = ⅀Assoc-C'-add↑-on-r m' n (B ∘ fsuc) (λ a' → C (fsuc a')) k kltᵣ' klt-inner'

        -- LHS reduces: apply on-inr at suc-level after bridging the index.
        lhs-step : Universe.⅀Assoc-C' 𝓝 (suc m' + n) B C
                     (sum (suc m') (B ∘ injL (suc m') n) + k , klt)
                 ≡ Universe.⅀Assoc-C' 𝓝 (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                                            (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k , klt-inner)
        lhs-step =
            cong (Universe.⅀Assoc-C' 𝓝 (suc m' + n) B C)
                 (Fin-fst-≡ {i = (sum (suc m') (B ∘ injL (suc m') n) + k , klt)}
                            {j = (B fzero + (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k)
                                 , <-k+ {k = B fzero} klt-inner)}
                            index-bridge)
          ∙ ⅀Assoc-C'-on-inr (m' + n) B C
                              (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k , klt-inner)

        -- Family bridge: pre-IH form to IH form.
        pre-IH-bridge :
            Universe.⅀Assoc-C' 𝓝 (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                                       (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k , klt-inner)
          ≡ Universe.⅀Assoc-C' 𝓝 (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a'))
                                       (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner')
        pre-IH-bridge = cong (Universe.⅀Assoc-C' 𝓝 (m' + n) (B ∘ fsuc) (λ a' → C (fsuc a')))
                              (Fin-fst-≡ (cong (_+ k) (cong (sum m') (funExt sum-prefix-fam-path))))

        -- Family bridge: IH RHS to final RHS.
        post-IH-bridge :
            Universe.⅀Assoc-C' 𝓝 n ((B ∘ fsuc) ∘ injR m' n)
                                       ((λ a' → C (fsuc a')) ∘ injR m' n) (k , kltᵣ')
          ≡ Universe.⅀Assoc-C' 𝓝 n (B ∘ injR (suc m') n) (C ∘ injR (suc m') n) (k , kltᵣ)
        post-IH-bridge i =
          Universe.⅀Assoc-C' 𝓝 n
            (λ a → Bᵣ-fam-path a (~ i))
            (λ a b → C (Fin-fst-≡ {i = injR (suc m') n a}
                                    {j = fsuc (injR m' n a)} refl (~ i))
                         b)
            (ΣPathP {A = λ _ → ℕ}
                     {B = λ j k' → k' < sum n (λ a → Bᵣ-fam-path a (~ j))}
                     (refl , isProp→PathP (λ _ → isProp≤) kltᵣ' kltᵣ) i)
      in lhs-step ∙ pre-IH-bridge ∙ IH ∙ post-IH-bridge

private
  -- joint-C' : the "merged" family on Fin (sum m Bₗ + sum n Bᵣ), defined by
  -- case-split on _≤?_ between left and right halves.
  opaque
    joint-C' : (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
             → Fin (sum m (B ∘ injL m n) + sum n (B ∘ injR m n)) → ℕ
    joint-C' m n B C (k , klt) with k ≤? sum m (B ∘ injL m n)
    ... | inl k<L = Universe.⅀Assoc-C' 𝓝 m (B ∘ injL m n) (C ∘ injL m n) (k , k<L)
    ... | inr L≤k =
      Universe.⅀Assoc-C' 𝓝 n (B ∘ injR m n) (C ∘ injR m n)
        (k ∸ sum m (B ∘ injL m n)
        , ∸-<-lemma (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n)) k klt L≤k)

  opaque
    unfolding sum-split ⅀Assoc-C'-add↑-on-l ⅀Assoc-C'-add↑-on-r joint-C'

    -- B-path-add↑ : the PathP from ⅀Assoc-C' 𝓝 (m+n) B C to joint-C' over sum-split.
    -- Built via funExtDep with case-split on _≤?_.
    -- Pointwise alignment lemma, pulled out for clarity.
    B-path-add↑-pointwise :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
      (a₀ : Fin (sum (m + n) B)) (a₁ : Fin (sum m (B ∘ injL m n) + sum n (B ∘ injR m n)))
      (fst-eq : fst a₀ ≡ fst a₁)
      → Universe.⅀Assoc-C' 𝓝 (m + n) B C a₀ ≡ joint-C' m n B C a₁
    B-path-add↑-pointwise m n B C a₀ a₁ fst-eq
      with fst a₁ ≤? sum m (B ∘ injL m n)
    ... | inl k<L =
      let
        bridged-klt : fst a₁ < sum (m + n) B
        bridged-klt = subst (fst a₁ <_) (sym (sum-split m n B))
                             (o<m→o<m+n (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                                          (fst a₁) k<L)
      in
        cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
             (Fin-fst-≡ {i = a₀} {j = (fst a₁ , bridged-klt)} fst-eq)
      ∙ ⅀Assoc-C'-add↑-on-l m n B C (fst a₁) k<L bridged-klt
    ... | inr L≤k =
      let
        k∸-bound : fst a₁ ∸ sum m (B ∘ injL m n) < sum n (B ∘ injR m n)
        k∸-bound = ∸-<-lemma (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                              (fst a₁) (snd a₁) L≤k
        bridged-klt : sum m (B ∘ injL m n) + (fst a₁ ∸ sum m (B ∘ injL m n)) < sum (m + n) B
        bridged-klt = subst (sum m (B ∘ injL m n) + (fst a₁ ∸ sum m (B ∘ injL m n)) <_)
                             (sym (sum-split m n B))
                             (<-k+ {k = sum m (B ∘ injL m n)} k∸-bound)
        index-eq : fst a₀ ≡ sum m (B ∘ injL m n) + (fst a₁ ∸ sum m (B ∘ injL m n))
        index-eq = fst-eq ∙ sym (∸-lemma L≤k)
      in
        cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
             (Fin-fst-≡ {i = a₀} {j = (sum m (B ∘ injL m n) + (fst a₁ ∸ sum m (B ∘ injL m n))
                                      , bridged-klt)}
                        index-eq)
      ∙ ⅀Assoc-C'-add↑-on-r m n B C (fst a₁ ∸ sum m (B ∘ injL m n)) k∸-bound bridged-klt

    B-path-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                → PathP (λ i → Fin (sum-split m n B i) → ℕ)
                        (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                        (joint-C' m n B C)
    B-path-add↑ m n B C = funExtDep λ {a₀} {a₁} a-path →
      B-path-add↑-pointwise m n B C a₀ a₁
        (sym (transport-Fin-fst (sum-split m n B) a₀) ∙ cong fst (fromPathP a-path))

  -- joint-kss: the corresponding kss-application function on the joint domain.
  opaque
    unfolding joint-C'

    joint-kss : (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
              → (ab : Fin (sum m (B ∘ injL m n) + sum n (B ∘ injR m n)))
              → IExpr (joint-C' m n B C ab)
    joint-kss m n B C kss (k , klt) with k ≤? sum m (B ∘ injL m n)
    ... | inl k<L =
      kss (injL m n (fst (sumFinFwd m (B ∘ injL m n) (k , k<L))))
          (snd (sumFinFwd m (B ∘ injL m n) (k , k<L)))
    ... | inr L≤k =
      kss (injR m n
            (fst (sumFinFwd n (B ∘ injR m n)
                              (k ∸ sum m (B ∘ injL m n)
                              , ∸-<-lemma (sum m (B ∘ injL m n))
                                            (sum n (B ∘ injR m n)) k klt L≤k))))
          (snd (sumFinFwd n (B ∘ injR m n)
                            (k ∸ sum m (B ∘ injL m n)
                            , ∸-<-lemma (sum m (B ∘ injL m n))
                                          (sum n (B ∘ injR m n)) k klt L≤k)))

  -- (m+n)-level Σ-pair Fubini for sumFinFwd. The four sumFinFwd-suc-*
  -- helpers wrap sumFinFwd's with-clause as propositional equations; their
  -- with-elaboration would otherwise leak the underlying _≟_ trichotomy
  -- into caller goal types.

  opaque
    sumFinFwd-suc-inl-fst :
      (n : ℕ) (B : Fin (suc n) → ℕ) (k : ℕ) (klt : k < sum (suc n) B)
      (k<B0 : k < B fzero)
      → fst (sumFinFwd (suc n) B (k , klt)) ≡ fzero
    sumFinFwd-suc-inl-fst n B k klt k<B0 with k ≤? B fzero
    ... | inl _    = refl
    ... | inr B0≤k = ⊥-rec (¬m<m (≤<-trans B0≤k k<B0))

  opaque
    unfolding sumFinFwd-suc-inl-fst
    -- PathP twin of sumFinFwd-suc-inl-fst, over the family it produces.
    sumFinFwd-suc-inl-snd :
      (n : ℕ) (B : Fin (suc n) → ℕ) (k : ℕ) (klt : k < sum (suc n) B)
      (k<B0 : k < B fzero)
      → PathP (λ i → Fin (B (sumFinFwd-suc-inl-fst n B k klt k<B0 i)))
              (snd (sumFinFwd (suc n) B (k , klt)))
              (k , k<B0)
    sumFinFwd-suc-inl-snd n B k klt k<B0 with k ≤? B fzero
    ... | inl k<B0' = ΣPathP {A = λ _ → ℕ} {B = λ _ k' → k' < B fzero}
                              (refl , isProp→PathP (λ _ → isProp≤) k<B0' k<B0)
    ... | inr B0≤k  = ⊥-rec (¬m<m (≤<-trans B0≤k k<B0))

  opaque
    sumFinFwd-suc-inr-fst :
      (n : ℕ) (B : Fin (suc n) → ℕ) (k : ℕ) (klt : k < sum (suc n) B)
      (B0≤k : B fzero ≤ k)
      → fst (sumFinFwd (suc n) B (k , klt))
      ≡ fsuc (fst (sumFinFwd n (B ∘ fsuc)
                                (k ∸ B fzero
                                , ∸-<-lemma (B fzero) (sum n (B ∘ fsuc)) k klt B0≤k)))
    sumFinFwd-suc-inr-fst n B k klt B0≤k with k ≤? B fzero
    ... | inl k<B0 = ⊥-rec (¬m<m (≤<-trans B0≤k k<B0))
    ... | inr B0≤k' = cong (λ p → fsuc (fst (sumFinFwd n (B ∘ fsuc)
                                                          (k ∸ B fzero
                                                          , ∸-<-lemma (B fzero) (sum n (B ∘ fsuc))
                                                                       k klt p))))
                            (isProp≤ B0≤k' B0≤k)

  opaque
    unfolding sumFinFwd-suc-inr-fst
    -- PathP twin of sumFinFwd-suc-inr-fst, over the family it produces.
    sumFinFwd-suc-inr-snd :
      (n : ℕ) (B : Fin (suc n) → ℕ) (k : ℕ) (klt : k < sum (suc n) B)
      (B0≤k : B fzero ≤ k)
      → PathP (λ i → Fin (B (sumFinFwd-suc-inr-fst n B k klt B0≤k i)))
              (snd (sumFinFwd (suc n) B (k , klt)))
              (snd (sumFinFwd n (B ∘ fsuc)
                                (k ∸ B fzero
                                , ∸-<-lemma (B fzero) (sum n (B ∘ fsuc)) k klt B0≤k)))
    sumFinFwd-suc-inr-snd n B k klt B0≤k with k ≤? B fzero
    ... | inl k<B0  = ⊥-rec (¬m<m (≤<-trans B0≤k k<B0))
    ... | inr B0≤k' =
      λ i → snd (sumFinFwd n (B ∘ fsuc)
                              (k ∸ B fzero
                              , ∸-<-lemma (B fzero) (sum n (B ∘ fsuc))
                                           k klt (isProp≤ B0≤k' B0≤k i)))

  opaque
    unfolding sumFinFwd-suc-inl-fst sumFinFwd-suc-inl-snd
              sumFinFwd-suc-inr-fst sumFinFwd-suc-inr-snd
    sumFinFwd-add↑-on-l :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (k : ℕ)
      (kltₗ : k < sum m (B ∘ injL m n))
      (klt : k < sum (m + n) B)
      → Σ[ p ∈ (fst (sumFinFwd (m + n) B (k , klt))
                ≡ injL m n (fst (sumFinFwd m (B ∘ injL m n) (k , kltₗ)))) ]
            PathP (λ i → Fin (B (p i)))
                  (snd (sumFinFwd (m + n) B (k , klt)))
                  (snd (sumFinFwd m (B ∘ injL m n) (k , kltₗ)))
    sumFinFwd-add↑-on-l zero    n B k kltₗ klt = ⊥-rec (¬-<-zero kltₗ)
    sumFinFwd-add↑-on-l (suc m') n B k kltₗ klt =
      -- Delegate to a where-helper taking the _≤?_ results as arguments,
      -- so the outer with-elaboration doesn't reach into sumFinFwd's body.
      cases (k ≤? B fzero) (k ≤? (B ∘ injL (suc m') n) fzero)
      where
        cases : ((k < B fzero) ⊎ (B fzero ≤ k))
              → ((k < (B ∘ injL (suc m') n) fzero)
                  ⊎ ((B ∘ injL (suc m') n) fzero ≤ k))
              → Σ[ p ∈ (fst (sumFinFwd (suc m' + n) B (k , klt))
                        ≡ injL (suc m') n
                            (fst (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))) ]
                    PathP (λ i → Fin (B (p i)))
                          (snd (sumFinFwd (suc m' + n) B (k , klt)))
                          (snd (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))
        cases (inl k<B0) (inl k<Bₗ0) =
          let
            fst-path : fst (sumFinFwd (suc m' + n) B (k , klt))
                     ≡ injL (suc m') n (fst (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))
            fst-path = sumFinFwd-suc-inl-fst (m' + n) B k klt k<B0
                     ∙ Fin-fst-≡ {i = fzero {k = m' + n}}
                                  {j = injL (suc m') n fzero} refl
                     ∙ cong (injL (suc m') n)
                            (sym (sumFinFwd-suc-inl-fst m' (B ∘ injL (suc m') n) k kltₗ k<Bₗ0))

            fst-snd-ℕ-eq : fst (snd (sumFinFwd (suc m' + n) B (k , klt)))
                         ≡ fst (snd (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))
            fst-snd-ℕ-eq =
                (λ i → fst (sumFinFwd-suc-inl-snd (m' + n) B k klt k<B0 i))
              ∙ sym (λ i → fst (sumFinFwd-suc-inl-snd m' (B ∘ injL (suc m') n)
                                                       k kltₗ k<Bₗ0 i))

            snd-path : PathP (λ i → Fin (B (fst-path i)))
                              (snd (sumFinFwd (suc m' + n) B (k , klt)))
                              (snd (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))
            snd-path = toPathP (Fin-fst-≡
                                  (transport-Fin-fst (cong B fst-path)
                                                      (snd (sumFinFwd (suc m' + n) B (k , klt)))
                                  ∙ fst-snd-ℕ-eq))
          in fst-path , snd-path
        cases (inl k<B0) (inr Bₗ0≤k) =
          ⊥-rec (¬m<m (≤<-trans Bₗ0≤k
                                  (subst (k <_)
                                         (cong B (Fin-fst-≡ {i = fzero}
                                                             {j = injL (suc m') n fzero} refl))
                                         k<B0)))
        cases (inr B0≤k) (inl k<Bₗ0) =
          ⊥-rec (¬m<m (≤<-trans B0≤k
                                  (subst (k <_)
                                         (sym (cong B (Fin-fst-≡ {i = fzero}
                                                                  {j = injL (suc m') n fzero}
                                                                  refl)))
                                         k<Bₗ0)))
        cases (inr B0≤k) (inr Bₗ0≤k) =
          let
            ∸-bridge : k ∸ B fzero ≡ k ∸ (B ∘ injL (suc m') n) fzero
            ∸-bridge = cong (k ∸_) (cong B (Fin-fst-≡ {i = fzero}
                                                        {j = injL (suc m') n fzero} refl))

            klt-rec : k ∸ B fzero < sum (m' + n) (B ∘ fsuc)
            klt-rec = ∸-<-lemma (B fzero) (sum (m' + n) (B ∘ fsuc)) k klt B0≤k

            kltₗ-rec : k ∸ (B ∘ injL (suc m') n) fzero
                     < sum m' ((B ∘ injL (suc m') n) ∘ fsuc)
            kltₗ-rec = ∸-<-lemma ((B ∘ injL (suc m') n) fzero)
                                  (sum m' ((B ∘ injL (suc m') n) ∘ fsuc)) k kltₗ Bₗ0≤k

            kltₗ-rec' : k ∸ B fzero < sum m' ((B ∘ fsuc) ∘ injL m' n)
            kltₗ-rec' = subst (k ∸ B fzero <_)
                               (cong (sum m')
                                     (funExt λ a → cong B (Fin-fst-≡
                                       {i = injL (suc m') n (fsuc a)}
                                       {j = fsuc (injL m' n a)} refl)))
                               (subst (_< sum m' ((B ∘ injL (suc m') n) ∘ fsuc))
                                      (sym ∸-bridge)
                                      kltₗ-rec)

            IH : Σ[ p ∈ (fst (sumFinFwd (m' + n) (B ∘ fsuc) (k ∸ B fzero , klt-rec))
                         ≡ injL m' n (fst (sumFinFwd m' ((B ∘ fsuc) ∘ injL m' n)
                                                          (k ∸ B fzero , kltₗ-rec')))) ]
                      PathP (λ i → Fin ((B ∘ fsuc) (p i)))
                            (snd (sumFinFwd (m' + n) (B ∘ fsuc) (k ∸ B fzero , klt-rec)))
                            (snd (sumFinFwd m' ((B ∘ fsuc) ∘ injL m' n)
                                              (k ∸ B fzero , kltₗ-rec')))
            IH = sumFinFwd-add↑-on-l m' n (B ∘ fsuc) (k ∸ B fzero) kltₗ-rec' klt-rec

            -- Bridge the family at sumFinFwd m' from ((B ∘ fsuc) ∘ injL m' n)
            -- to ((B ∘ injL (suc m') n) ∘ fsuc).
            fam-eq : (a : Fin m') → (B ∘ fsuc) (injL m' n a) ≡ (B ∘ injL (suc m') n) (fsuc a)
            fam-eq a = cong B (Fin-fst-≡ {i = fsuc (injL m' n a)}
                                           {j = injL (suc m') n (fsuc a)} refl)

            rec-input-PathP : PathP (λ i → Fin (sum m' (λ a → fam-eq a i)))
                                     (k ∸ B fzero , kltₗ-rec')
                                     (k ∸ (B ∘ injL (suc m') n) fzero , kltₗ-rec)
            rec-input-PathP = ΣPathP {A = λ _ → ℕ}
                                      {B = λ i k' → k' < sum m' (λ a → fam-eq a i)}
                                      (∸-bridge , isProp→PathP (λ _ → isProp≤)
                                                               kltₗ-rec' kltₗ-rec)

            rec-bridge : PathP (λ i → Σ (Fin m') (λ a → Fin (fam-eq a i)))
                                (sumFinFwd m' ((B ∘ fsuc) ∘ injL m' n) (k ∸ B fzero , kltₗ-rec'))
                                (sumFinFwd m' ((B ∘ injL (suc m') n) ∘ fsuc)
                                              (k ∸ (B ∘ injL (suc m') n) fzero , kltₗ-rec))
            rec-bridge i = sumFinFwd m' (λ a → fam-eq a i) (rec-input-PathP i)

            rec-bridge-fst : Path (Fin m')
                                    (fst (sumFinFwd m' ((B ∘ fsuc) ∘ injL m' n)
                                                        (k ∸ B fzero , kltₗ-rec')))
                                    (fst (sumFinFwd m' ((B ∘ injL (suc m') n) ∘ fsuc)
                                                        (k ∸ (B ∘ injL (suc m') n) fzero
                                                        , kltₗ-rec)))
            rec-bridge-fst i = fst (rec-bridge i)

            fst-path : fst (sumFinFwd (suc m' + n) B (k , klt))
                     ≡ injL (suc m') n (fst (sumFinFwd (suc m') (B ∘ injL (suc m') n)
                                                                     (k , kltₗ)))
            fst-path = sumFinFwd-suc-inr-fst (m' + n) B k klt B0≤k
                      ∙ cong fsuc (IH .fst)
                      ∙ cong fsuc (cong (injL m' n) rec-bridge-fst)
                      ∙ Fin-fst-≡ refl
                      ∙ cong (injL (suc m') n)
                             (sym (sumFinFwd-suc-inr-fst m' (B ∘ injL (suc m') n) k kltₗ Bₗ0≤k))

            fst-of-snd-LHS-eq :
                fst (snd (sumFinFwd (suc m' + n) B (k , klt)))
              ≡ fst (snd (sumFinFwd (m' + n) (B ∘ fsuc) (k ∸ B fzero , klt-rec)))
            fst-of-snd-LHS-eq i = fst (sumFinFwd-suc-inr-snd (m' + n) B k klt B0≤k i)

            IH-snd-fst-eq :
                fst (snd (sumFinFwd (m' + n) (B ∘ fsuc) (k ∸ B fzero , klt-rec)))
              ≡ fst (snd (sumFinFwd m' ((B ∘ fsuc) ∘ injL m' n) (k ∸ B fzero , kltₗ-rec')))
            IH-snd-fst-eq i = fst (IH .snd i)

            rec-bridge-snd-fst-eq :
                fst (snd (sumFinFwd m' ((B ∘ fsuc) ∘ injL m' n) (k ∸ B fzero , kltₗ-rec')))
              ≡ fst (snd (sumFinFwd m' ((B ∘ injL (suc m') n) ∘ fsuc)
                                      (k ∸ (B ∘ injL (suc m') n) fzero , kltₗ-rec)))
            rec-bridge-snd-fst-eq i = fst (snd (rec-bridge i))

            fst-of-snd-RHS-eq :
                fst (snd (sumFinFwd m' ((B ∘ injL (suc m') n) ∘ fsuc)
                                      (k ∸ (B ∘ injL (suc m') n) fzero , kltₗ-rec)))
              ≡ fst (snd (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))
            fst-of-snd-RHS-eq i = fst (sumFinFwd-suc-inr-snd m' (B ∘ injL (suc m') n)
                                                              k kltₗ Bₗ0≤k (~ i))

            fst-snd-ℕ-eq : fst (snd (sumFinFwd (suc m' + n) B (k , klt)))
                         ≡ fst (snd (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))
            fst-snd-ℕ-eq = fst-of-snd-LHS-eq ∙ IH-snd-fst-eq
                         ∙ rec-bridge-snd-fst-eq ∙ fst-of-snd-RHS-eq

            snd-path : PathP (λ i → Fin (B (fst-path i)))
                              (snd (sumFinFwd (suc m' + n) B (k , klt)))
                              (snd (sumFinFwd (suc m') (B ∘ injL (suc m') n) (k , kltₗ)))
            snd-path = toPathP (Fin-fst-≡
                                  (transport-Fin-fst (cong B fst-path)
                                                      (snd (sumFinFwd (suc m' + n) B (k , klt)))
                                  ∙ fst-snd-ℕ-eq))
          in fst-path , snd-path

  opaque
    unfolding sumFinFwd-suc-inr-fst sumFinFwd-suc-inr-snd
    sumFinFwd-add↑-on-r :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (k : ℕ)
      (kltᵣ : k < sum n (B ∘ injR m n))
      (klt : sum m (B ∘ injL m n) + k < sum (m + n) B)
      → Σ[ p ∈ (fst (sumFinFwd (m + n) B (sum m (B ∘ injL m n) + k , klt))
                ≡ injR m n (fst (sumFinFwd n (B ∘ injR m n) (k , kltᵣ)))) ]
            PathP (λ i → Fin (B (p i)))
                  (snd (sumFinFwd (m + n) B (sum m (B ∘ injL m n) + k , klt)))
                  (snd (sumFinFwd n (B ∘ injR m n) (k , kltᵣ)))
    sumFinFwd-add↑-on-r zero    n B k kltᵣ klt =
      -- m = 0: index is 0 + k = k, and injR 0 n is propositionally identity.
      let
        fam-path : (a : Fin n) → B a ≡ (B ∘ injR zero n) a
        fam-path a = cong B (Fin-fst-≡ {i = a} {j = injR zero n a} refl)

        rec-input-PathP : PathP (λ i → Fin (sum n (λ a → fam-path a i))) (k , klt) (k , kltᵣ)
        rec-input-PathP = ΣPathP {A = λ _ → ℕ}
                                  {B = λ i k' → k' < sum n (λ a → fam-path a i)}
                                  (refl , isProp→PathP (λ _ → isProp≤) klt kltᵣ)

        rec-bridge : PathP (λ i → Σ (Fin n) (λ a → Fin (fam-path a i)))
                            (sumFinFwd n B (k , klt))
                            (sumFinFwd n (B ∘ injR zero n) (k , kltᵣ))
        rec-bridge i = sumFinFwd n (λ a → fam-path a i) (rec-input-PathP i)

        fst-path : fst (sumFinFwd n B (k , klt))
                 ≡ injR zero n (fst (sumFinFwd n (B ∘ injR zero n) (k , kltᵣ)))
        fst-path = (λ i → fst (rec-bridge i))
                 ∙ Fin-fst-≡ {i = fst (sumFinFwd n (B ∘ injR zero n) (k , kltᵣ))}
                              {j = injR zero n (fst (sumFinFwd n (B ∘ injR zero n) (k , kltᵣ)))}
                              refl

        fst-snd-ℕ-eq : fst (snd (sumFinFwd n B (k , klt)))
                     ≡ fst (snd (sumFinFwd n (B ∘ injR zero n) (k , kltᵣ)))
        fst-snd-ℕ-eq i = fst (snd (rec-bridge i))

        snd-path : PathP (λ i → Fin (B (fst-path i)))
                          (snd (sumFinFwd n B (k , klt)))
                          (snd (sumFinFwd n (B ∘ injR zero n) (k , kltᵣ)))
        snd-path = toPathP (Fin-fst-≡
                              (transport-Fin-fst (cong B fst-path)
                                                  (snd (sumFinFwd n B (k , klt)))
                              ∙ fst-snd-ℕ-eq))
      in fst-path , snd-path
    sumFinFwd-add↑-on-r (suc m') n B k kltᵣ klt =
      -- Index: sum (suc m') Bₗ + k; always in inr branch of _≤?_ at top level.
      let
        Bₗ-fzero-eq : B fzero ≡ (B ∘ injL (suc m') n) fzero
        Bₗ-fzero-eq = cong B (Fin-fst-≡ {i = fzero} {j = injL (suc m') n fzero} refl)

        index-bridge : sum (suc m') (B ∘ injL (suc m') n) + k
                     ≡ B fzero + (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k)
        index-bridge = cong (_+ k) (cong (_+ sum m' ((B ∘ injL (suc m') n) ∘ fsuc))
                                          (sym Bₗ-fzero-eq))
                      ∙ sym (+-assoc (B fzero) (sum m' ((B ∘ injL (suc m') n) ∘ fsuc)) k)

        full-klt : B fzero + (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k)
                 < B fzero + sum (m' + n) (B ∘ fsuc)
        full-klt = subst (_< B fzero + sum (m' + n) (B ∘ fsuc)) index-bridge klt

        klt-inner : sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k < sum (m' + n) (B ∘ fsuc)
        klt-inner = <-k+-cancel {k = B fzero} full-klt

        sum-prefix-fam-path : (a : Fin m')
                            → (B ∘ injL (suc m') n) (fsuc a) ≡ (B ∘ fsuc) (injL m' n a)
        sum-prefix-fam-path a = cong B (Fin-fst-≡ {i = injL (suc m') n (fsuc a)}
                                                     {j = fsuc (injL m' n a)} refl)

        klt-inner' : sum m' ((B ∘ fsuc) ∘ injL m' n) + k < sum (m' + n) (B ∘ fsuc)
        klt-inner' = subst (_< sum (m' + n) (B ∘ fsuc))
                            (cong (_+ k) (cong (sum m') (funExt sum-prefix-fam-path)))
                            klt-inner

        Bᵣ-fsuc-eq : (a : Fin n)
                    → (B ∘ injR (suc m') n) a ≡ (B ∘ fsuc) (injR m' n a)
        Bᵣ-fsuc-eq a = cong B (Fin-fst-≡ {i = injR (suc m') n a}
                                            {j = fsuc (injR m' n a)} refl)

        kltᵣ' : k < sum n ((B ∘ fsuc) ∘ injR m' n)
        kltᵣ' = subst (k <_) (cong (sum n) (funExt Bᵣ-fsuc-eq)) kltᵣ

        IH : Σ[ p ∈ (fst (sumFinFwd (m' + n) (B ∘ fsuc)
                                     (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner'))
                     ≡ injR m' n (fst (sumFinFwd n ((B ∘ fsuc) ∘ injR m' n) (k , kltᵣ')))) ]
                  PathP (λ i → Fin ((B ∘ fsuc) (p i)))
                        (snd (sumFinFwd (m' + n) (B ∘ fsuc)
                                          (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner')))
                        (snd (sumFinFwd n ((B ∘ fsuc) ∘ injR m' n) (k , kltᵣ')))
        IH = sumFinFwd-add↑-on-r m' n (B ∘ fsuc) k kltᵣ' klt-inner'

        -- Bound: B fzero ≤ sum (suc m') (B∘injL (suc m') n) + k (always inr at top-level).
        B0≤sum-+-k : B fzero ≤ sum (suc m') (B ∘ injL (suc m') n) + k
        B0≤sum-+-k = ≤-trans (≤-reflexive Bₗ-fzero-eq)
                              (≤-trans ≤SumLeft ≤SumLeft)

        -- Bound proof for the inner recursion after sumFinFwd-suc-inr-fst.
        rec-arg-bound : sum (suc m') (B ∘ injL (suc m') n) + k ∸ B fzero
                      < sum (m' + n) (B ∘ fsuc)
        rec-arg-bound = ∸-<-lemma (B fzero) (sum (m' + n) (B ∘ fsuc))
                                   (sum (suc m') (B ∘ injL (suc m') n) + k) klt B0≤sum-+-k

        -- Bridge the inner ℕ index from "sum (suc m') Bₗ + k - B fzero"
        -- to "sum m' ((B∘fsuc)∘injL m' n) + k". Uses index-bridge to
        -- expose (B fzero + ...), commutes, applies m+n∸n=m, then
        -- bridges the family via sum-prefix-fam-path.
        inner-index-bridge : sum (suc m') (B ∘ injL (suc m') n) + k ∸ B fzero
                           ≡ sum m' ((B ∘ fsuc) ∘ injL m' n) + k
        inner-index-bridge =
            cong (_∸ B fzero) index-bridge
          ∙ cong (_∸ B fzero)
                 (+-comm (B fzero) (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k))
          ∙ m+n∸n=m (B fzero) (sum m' ((B ∘ injL (suc m') n) ∘ fsuc) + k)
          ∙ cong (_+ k) (cong (sum m') (funExt sum-prefix-fam-path))

        -- Path between bound proofs (via isProp≤).
        rec-arg-PathP : PathP (λ i → Fin (sum (m' + n) (B ∘ fsuc)))
                              (sum (suc m') (B ∘ injL (suc m') n) + k ∸ B fzero , rec-arg-bound)
                              (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner')
        rec-arg-PathP = ΣPathP {A = λ _ → ℕ}
                                {B = λ _ k' → k' < sum (m' + n) (B ∘ fsuc)}
                                (inner-index-bridge ,
                                 isProp→PathP (λ _ → isProp≤) rec-arg-bound klt-inner')

        sFF-arg-bridge : PathP (λ i → Σ[ a ∈ Fin (m' + n) ] Fin ((B ∘ fsuc) a))
                               (sumFinFwd (m' + n) (B ∘ fsuc)
                                          (sum (suc m') (B ∘ injL (suc m') n) + k ∸ B fzero
                                          , rec-arg-bound))
                               (sumFinFwd (m' + n) (B ∘ fsuc)
                                          (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner'))
        sFF-arg-bridge i = sumFinFwd (m' + n) (B ∘ fsuc) (rec-arg-PathP i)

        -- Bridge from (B∘injR (suc m') n) to (B∘fsuc) ∘ injR m' n via Bᵣ-fsuc-eq.
        Bᵣ-bridge-input-PathP :
          PathP (λ i → Fin (sum n (λ a → Bᵣ-fsuc-eq a i))) (k , kltᵣ) (k , kltᵣ')
        Bᵣ-bridge-input-PathP = ΣPathP {A = λ _ → ℕ}
                                        {B = λ i k' → k' < sum n (λ a → Bᵣ-fsuc-eq a i)}
                                        (refl , isProp→PathP (λ _ → isProp≤) kltᵣ kltᵣ')

        Bᵣ-bridge : PathP (λ i → Σ (Fin n) (λ a → Fin (Bᵣ-fsuc-eq a i)))
                          (sumFinFwd n (B ∘ injR (suc m') n) (k , kltᵣ))
                          (sumFinFwd n ((B ∘ fsuc) ∘ injR m' n) (k , kltᵣ'))
        Bᵣ-bridge i = sumFinFwd n (λ a → Bᵣ-fsuc-eq a i) (Bᵣ-bridge-input-PathP i)

        -- fst-path: chain.
        fst-path : fst (sumFinFwd (suc m' + n) B (sum (suc m') (B ∘ injL (suc m') n) + k , klt))
                 ≡ injR (suc m') n (fst (sumFinFwd n (B ∘ injR (suc m') n) (k , kltᵣ)))
        fst-path =
            sumFinFwd-suc-inr-fst (m' + n) B
                                  (sum (suc m') (B ∘ injL (suc m') n) + k) klt B0≤sum-+-k
          ∙ cong fsuc (λ i → fst (sFF-arg-bridge i))
          ∙ cong fsuc (IH .fst)
          ∙ cong fsuc (cong (injR m' n) (sym (λ i → fst (Bᵣ-bridge i))))
          ∙ Fin-fst-≡ {i = fsuc (injR m' n (fst (sumFinFwd n (B ∘ injR (suc m') n) (k , kltᵣ))))}
                      {j = injR (suc m') n (fst (sumFinFwd n (B ∘ injR (suc m') n) (k , kltᵣ)))}
                      refl

        -- Underlying ℕ-equation chain for snd.
        fst-of-snd-LHS-eq :
            fst (snd (sumFinFwd (suc m' + n) B (sum (suc m') (B ∘ injL (suc m') n) + k , klt)))
          ≡ fst (snd (sumFinFwd (m' + n) (B ∘ fsuc)
                                (sum (suc m') (B ∘ injL (suc m') n) + k ∸ B fzero
                                , rec-arg-bound)))
        fst-of-snd-LHS-eq i =
          fst (sumFinFwd-suc-inr-snd (m' + n) B
                 (sum (suc m') (B ∘ injL (suc m') n) + k) klt B0≤sum-+-k i)

        sFF-arg-snd-fst-eq :
            fst (snd (sumFinFwd (m' + n) (B ∘ fsuc)
                                (sum (suc m') (B ∘ injL (suc m') n) + k ∸ B fzero
                                , rec-arg-bound)))
          ≡ fst (snd (sumFinFwd (m' + n) (B ∘ fsuc)
                                (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner')))
        sFF-arg-snd-fst-eq i = fst (snd (sFF-arg-bridge i))

        IH-snd-fst-eq :
            fst (snd (sumFinFwd (m' + n) (B ∘ fsuc)
                                (sum m' ((B ∘ fsuc) ∘ injL m' n) + k , klt-inner')))
          ≡ fst (snd (sumFinFwd n ((B ∘ fsuc) ∘ injR m' n) (k , kltᵣ')))
        IH-snd-fst-eq i = fst (IH .snd i)

        Bᵣ-bridge-snd-fst-eq :
            fst (snd (sumFinFwd n ((B ∘ fsuc) ∘ injR m' n) (k , kltᵣ')))
          ≡ fst (snd (sumFinFwd n (B ∘ injR (suc m') n) (k , kltᵣ)))
        Bᵣ-bridge-snd-fst-eq i = fst (snd (Bᵣ-bridge (~ i)))

        fst-snd-ℕ-eq : fst (snd (sumFinFwd (suc m' + n) B
                                            (sum (suc m') (B ∘ injL (suc m') n) + k , klt)))
                     ≡ fst (snd (sumFinFwd n (B ∘ injR (suc m') n) (k , kltᵣ)))
        fst-snd-ℕ-eq = fst-of-snd-LHS-eq ∙ sFF-arg-snd-fst-eq
                     ∙ IH-snd-fst-eq ∙ Bᵣ-bridge-snd-fst-eq

        snd-path : PathP (λ i → Fin (B (fst-path i)))
                          (snd (sumFinFwd (suc m' + n) B
                                            (sum (suc m') (B ∘ injL (suc m') n) + k , klt)))
                          (snd (sumFinFwd n (B ∘ injR (suc m') n) (k , kltᵣ)))
        snd-path = toPathP (Fin-fst-≡
                              (transport-Fin-fst (cong B fst-path)
                                                  (snd (sumFinFwd (suc m' + n) B
                                                          (sum (suc m') (B ∘ injL (suc m') n) + k
                                                          , klt)))
                              ∙ fst-snd-ℕ-eq))
      in fst-path , snd-path

  -- joint-form bridges: joint-C'/joint-kss restricted to injL or injR
  -- reduce to the m-side (resp. n-side) ⅀Assoc-C'/kss-application.
  -- (m+n)-level analogues of ⅀Assoc-C'-on-inl/inr and kss-bridge-L/R.

  opaque
    unfolding joint-C'
    joint-C'-on-injL : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                       (kp : Fin (sum m (B ∘ injL m n)))
                     → joint-C' m n B C
                         (injL (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n)) kp)
                     ≡ Universe.⅀Assoc-C' 𝓝 m (B ∘ injL m n) (C ∘ injL m n) kp
    joint-C'-on-injL m n B C (k , k<L-input)
      with k ≤? sum m (B ∘ injL m n)
    ... | inl k<L = cong (Universe.⅀Assoc-C' 𝓝 m (B ∘ injL m n) (C ∘ injL m n))
                          (Fin-fst-≡ {i = (k , k<L)} {j = (k , k<L-input)} refl)
    ... | inr L≤k = ⊥-rec (¬m<m (≤<-trans L≤k k<L-input))

  opaque
    unfolding joint-C'
    joint-C'-on-injR : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                       (kp : Fin (sum n (B ∘ injR m n)))
                     → joint-C' m n B C
                         (injR (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n)) kp)
                     ≡ Universe.⅀Assoc-C' 𝓝 n (B ∘ injR m n) (C ∘ injR m n) kp
    joint-C'-on-injR m n B C (k , k<R-input)
      with (sum m (B ∘ injL m n) + k) ≤? sum m (B ∘ injL m n)
    ... | inl L+k<L = ⊥-rec (¬m+n<m {m = sum m (B ∘ injL m n)} {n = k} L+k<L)
    ... | inr L≤L+k =
      cong (Universe.⅀Assoc-C' 𝓝 n (B ∘ injR m n) (C ∘ injR m n))
           (Fin-fst-≡ {i = (sum m (B ∘ injL m n) + k ∸ sum m (B ∘ injL m n) , _)}
                      {j = (k , k<R-input)}
                      ((cong (_∸ sum m (B ∘ injL m n))
                             (+-comm (sum m (B ∘ injL m n)) k))
                       ∙ m+n∸n=m (sum m (B ∘ injL m n)) k))

  opaque
    unfolding joint-kss joint-C'-on-injL
    joint-kss-on-injL : (m n : ℕ) (B : Fin (m + n) → ℕ)
                        (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                        (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                        (kp : Fin (sum m (B ∘ injL m n)))
                      → PathP (λ i → IExpr (joint-C'-on-injL m n B C kp i))
                              (joint-kss m n B C kss
                                         (injL (sum m (B ∘ injL m n))
                                                (sum n (B ∘ injR m n)) kp))
                              (kss (injL m n (fst (sumFinFwd m (B ∘ injL m n) kp)))
                                   (snd (sumFinFwd m (B ∘ injL m n) kp)))
    joint-kss-on-injL m n B C kss (k , k<L-input)
      with k ≤? sum m (B ∘ injL m n)
    ... | inl k<L =
      λ i →
        kss (injL m n (fst (sumFinFwd m (B ∘ injL m n)
                                       (Fin-fst-≡ {i = (k , k<L)}
                                                   {j = (k , k<L-input)} refl i))))
            (snd (sumFinFwd m (B ∘ injL m n)
                              (Fin-fst-≡ {i = (k , k<L)}
                                          {j = (k , k<L-input)} refl i)))
    ... | inr L≤k = ⊥-rec (¬m<m (≤<-trans L≤k k<L-input))

  opaque
    unfolding joint-kss joint-C'-on-injR
    joint-kss-on-injR : (m n : ℕ) (B : Fin (m + n) → ℕ)
                        (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                        (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                        (kp : Fin (sum n (B ∘ injR m n)))
                      → PathP (λ i → IExpr (joint-C'-on-injR m n B C kp i))
                              (joint-kss m n B C kss
                                         (injR (sum m (B ∘ injL m n))
                                                (sum n (B ∘ injR m n)) kp))
                              (kss (injR m n (fst (sumFinFwd n (B ∘ injR m n) kp)))
                                   (snd (sumFinFwd n (B ∘ injR m n) kp)))
    joint-kss-on-injR m n B C kss (k , k<R-input)
      with (sum m (B ∘ injL m n) + k) ≤? sum m (B ∘ injL m n)
    ... | inl L+k<L = ⊥-rec (¬m+n<m {m = sum m (B ∘ injL m n)} {n = k} L+k<L)
    ... | inr L≤L+k =
      let
        idx-bridge : sum m (B ∘ injL m n) + k ∸ sum m (B ∘ injL m n) ≡ k
        idx-bridge = (cong (_∸ sum m (B ∘ injL m n))
                            (+-comm (sum m (B ∘ injL m n)) k))
                   ∙ m+n∸n=m (sum m (B ∘ injL m n)) k
      in λ i →
           kss (injR m n
                 (fst (sumFinFwd n (B ∘ injR m n)
                                  (Fin-fst-≡ {i = (sum m (B ∘ injL m n) + k
                                                    ∸ sum m (B ∘ injL m n) , _)}
                                              {j = (k , k<R-input)}
                                              idx-bridge i))))
               (snd (sumFinFwd n (B ∘ injR m n)
                                (Fin-fst-≡ {i = (sum m (B ∘ injL m n) + k
                                                  ∸ sum m (B ∘ injL m n) , _)}
                                            {j = (k , k<R-input)}
                                            idx-bridge i)))

  -- es-path-add↑: kss-application PathP analogue of B-path-add↑.

  opaque
    unfolding sum-split

    es-path-add↑-pointwise :
      (m n : ℕ) (B : Fin (m + n) → ℕ) (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
      (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
      {a₀ : Fin (sum (m + n) B)}
      {a₁ : Fin (sum m (B ∘ injL m n) + sum n (B ∘ injR m n))}
      (a-path : PathP (λ i → Fin (sum-split m n B i)) a₀ a₁)
      → PathP (λ i → IExpr (B-path-add↑ m n B C i (a-path i)))
              (kss (fst (sumFinFwd (m + n) B a₀)) (snd (sumFinFwd (m + n) B a₀)))
              (joint-kss m n B C kss a₁)
    es-path-add↑-pointwise m n B C kss {a₀} {a₁} a-path
      with fst a₁ ≤? sum m (B ∘ injL m n)
    ... | inl k<L =
      let
        fst-eq : fst a₀ ≡ fst a₁
        fst-eq = sym (transport-Fin-fst (sum-split m n B) a₀)
               ∙ cong fst (fromPathP a-path)
        bridged-klt : fst a₁ < sum (m + n) B
        bridged-klt = subst (fst a₁ <_) (sym (sum-split m n B))
                             (o<m→o<m+n (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
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
        -- Step 2: kss at (m+n) sFF → kss at injL m n (m sFF). Bridge via sumFinFwd-add↑-on-l.
        sFF-on-l = sumFinFwd-add↑-on-l m n B (fst a₁) k<L bridged-klt
        step2 : PathP (λ i → IExpr (C (sFF-on-l .fst i) (sFF-on-l .snd i)))
                       (kss (fst (sumFinFwd (m + n) B (fst a₁ , bridged-klt)))
                            (snd (sumFinFwd (m + n) B (fst a₁ , bridged-klt))))
                       (kss (injL m n (fst (sumFinFwd m (B ∘ injL m n) (fst a₁ , k<L))))
                            (snd (sumFinFwd m (B ∘ injL m n) (fst a₁ , k<L))))
        step2 i = kss (sFF-on-l .fst i) (sFF-on-l .snd i)
        -- Step 3: kss (injL m n (fst sFF')) (snd sFF') → joint-kss kss (injL ... (fst a₁, k<L)).
        --   Use symP of joint-kss-on-injL.
        step3 : PathP (λ i → IExpr (joint-C'-on-injL m n B C (fst a₁ , k<L) (~ i)))
                       (kss (injL m n (fst (sumFinFwd m (B ∘ injL m n) (fst a₁ , k<L))))
                            (snd (sumFinFwd m (B ∘ injL m n) (fst a₁ , k<L))))
                       (joint-kss m n B C kss
                                  (injL (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                                         (fst a₁ , k<L)))
        step3 = symP (joint-kss-on-injL m n B C kss (fst a₁ , k<L))
        -- Step 4: joint-kss (injL ... (fst a₁, k<L)) → joint-kss a₁. Bridge via Fin-fst-≡.
        align-a₁ : injL (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n)) (fst a₁ , k<L) ≡ a₁
        align-a₁ = Fin-fst-≡ {i = injL (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                                       (fst a₁ , k<L)}
                              {j = a₁} refl
        step4 : PathP (λ i → IExpr (joint-C' m n B C (align-a₁ i)))
                       (joint-kss m n B C kss
                                  (injL (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                                         (fst a₁ , k<L)))
                       (joint-kss m n B C kss a₁)
        step4 i = joint-kss m n B C kss (align-a₁ i)
        composed : PathP (λ i → IExpr (((cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                                              (Fin-fst-≡ {i = a₀}
                                                          {j = (fst a₁ , bridged-klt)} fst-eq))
                                        ∙ (λ i → C (sFF-on-l .fst i) (sFF-on-l .snd i))
                                        ∙ (λ i → joint-C'-on-injL m n B C
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
      in subst (λ p → PathP (λ i → IExpr (p i))
                            (kss (fst (sumFinFwd (m + n) B a₀))
                                 (snd (sumFinFwd (m + n) B a₀)))
                            (joint-kss m n B C kss a₁))
               (isSetℕ _ _ ((cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                                  (Fin-fst-≡ {i = a₀}
                                              {j = (fst a₁ , bridged-klt)} fst-eq))
                            ∙ (λ i → C (sFF-on-l .fst i) (sFF-on-l .snd i))
                            ∙ (λ i → joint-C'-on-injL m n B C (fst a₁ , k<L) (~ i))
                            ∙ cong (joint-C' m n B C) align-a₁)
                          target-path)
               composed
    ... | inr L≤k =
      let
        fst-eq : fst a₀ ≡ fst a₁
        fst-eq = sym (transport-Fin-fst (sum-split m n B) a₀)
               ∙ cong fst (fromPathP a-path)
        k∸-bound : fst a₁ ∸ sum m (B ∘ injL m n) < sum n (B ∘ injR m n)
        k∸-bound = ∸-<-lemma (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                              (fst a₁) (snd a₁) L≤k
        bridged-klt : sum m (B ∘ injL m n) + (fst a₁ ∸ sum m (B ∘ injL m n))
                    < sum (m + n) B
        bridged-klt = subst (sum m (B ∘ injL m n) + (fst a₁ ∸ sum m (B ∘ injL m n)) <_)
                             (sym (sum-split m n B))
                             (<-k+ {k = sum m (B ∘ injL m n)} k∸-bound)
        index-eq : fst a₀ ≡ sum m (B ∘ injL m n) + (fst a₁ ∸ sum m (B ∘ injL m n))
        index-eq = fst-eq ∙ sym (∸-lemma L≤k)
        step1 : PathP (λ i → IExpr (Universe.⅀Assoc-C' 𝓝 (m + n) B C
                                       (Fin-fst-≡
                                          {i = a₀}
                                          {j = (sum m (B ∘ injL m n)
                                                + (fst a₁ ∸ sum m (B ∘ injL m n))
                                               , bridged-klt)}
                                          index-eq i)))
                       (kss (fst (sumFinFwd (m + n) B a₀))
                            (snd (sumFinFwd (m + n) B a₀)))
                       (kss (fst (sumFinFwd (m + n) B
                                            (sum m (B ∘ injL m n)
                                             + (fst a₁ ∸ sum m (B ∘ injL m n))
                                            , bridged-klt)))
                            (snd (sumFinFwd (m + n) B _)))
        step1 i =
          kss (fst (sumFinFwd (m + n) B
                              (Fin-fst-≡ {i = a₀}
                                          {j = (sum m (B ∘ injL m n)
                                                + (fst a₁ ∸ sum m (B ∘ injL m n))
                                               , bridged-klt)}
                                          index-eq i)))
              (snd (sumFinFwd (m + n) B
                              (Fin-fst-≡ {i = a₀}
                                          {j = (sum m (B ∘ injL m n)
                                                + (fst a₁ ∸ sum m (B ∘ injL m n))
                                               , bridged-klt)}
                                          index-eq i)))
        sFF-on-r = sumFinFwd-add↑-on-r m n B (fst a₁ ∸ sum m (B ∘ injL m n))
                                       k∸-bound bridged-klt
        step2 : PathP (λ i → IExpr (C (sFF-on-r .fst i) (sFF-on-r .snd i)))
                       (kss (fst (sumFinFwd (m + n) B
                                            (sum m (B ∘ injL m n)
                                             + (fst a₁ ∸ sum m (B ∘ injL m n))
                                            , bridged-klt)))
                            (snd (sumFinFwd (m + n) B _)))
                       (kss (injR m n (fst (sumFinFwd n (B ∘ injR m n)
                                                       (fst a₁ ∸ sum m (B ∘ injL m n)
                                                       , k∸-bound))))
                            (snd (sumFinFwd n (B ∘ injR m n) _)))
        step2 i = kss (sFF-on-r .fst i) (sFF-on-r .snd i)
        step3 : PathP (λ i → IExpr (joint-C'-on-injR m n B C
                                       (fst a₁ ∸ sum m (B ∘ injL m n) , k∸-bound) (~ i)))
                       (kss (injR m n (fst (sumFinFwd n (B ∘ injR m n)
                                                       (fst a₁ ∸ sum m (B ∘ injL m n)
                                                       , k∸-bound))))
                            (snd (sumFinFwd n (B ∘ injR m n) _)))
                       (joint-kss m n B C kss
                                  (injR (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                                         (fst a₁ ∸ sum m (B ∘ injL m n) , k∸-bound)))
        step3 = symP (joint-kss-on-injR m n B C kss
                                         (fst a₁ ∸ sum m (B ∘ injL m n) , k∸-bound))
        align-a₁ : injR (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                        (fst a₁ ∸ sum m (B ∘ injL m n) , k∸-bound) ≡ a₁
        align-a₁ = Fin-fst-≡ {i = injR (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                                        (fst a₁ ∸ sum m (B ∘ injL m n) , k∸-bound)}
                              {j = a₁} (∸-lemma L≤k)
        step4 : PathP (λ i → IExpr (joint-C' m n B C (align-a₁ i)))
                       (joint-kss m n B C kss
                                  (injR (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                                         (fst a₁ ∸ sum m (B ∘ injL m n) , k∸-bound)))
                       (joint-kss m n B C kss a₁)
        step4 i = joint-kss m n B C kss (align-a₁ i)
        composed = compPathP' {B = IExpr} step1
                     (compPathP' {B = IExpr} step2
                       (compPathP' {B = IExpr} step3 step4))
        target-path : Universe.⅀Assoc-C' 𝓝 (m + n) B C a₀ ≡ joint-C' m n B C a₁
        target-path = λ i → B-path-add↑ m n B C i (a-path i)
      in subst (λ p → PathP (λ i → IExpr (p i))
                            (kss (fst (sumFinFwd (m + n) B a₀))
                                 (snd (sumFinFwd (m + n) B a₀)))
                            (joint-kss m n B C kss a₁))
               (isSetℕ _ _ ((cong (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
                                  (Fin-fst-≡
                                     {i = a₀}
                                     {j = (sum m (B ∘ injL m n)
                                           + (fst a₁ ∸ sum m (B ∘ injL m n))
                                          , bridged-klt)}
                                     index-eq))
                            ∙ (λ i → C (sFF-on-r .fst i) (sFF-on-r .snd i))
                            ∙ (λ i → joint-C'-on-injR m n B C
                                        (fst a₁ ∸ sum m (B ∘ injL m n) , k∸-bound) (~ i))
                            ∙ cong (joint-C' m n B C) align-a₁)
                          target-path)
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

  -- IExpr-comp distributivity over add↑: just subst-filler over the
  -- definitional IExpr-comp .(m + n) B (add↑ e₁ e₂) ks reduction.

  opaque
    unfolding sum-split
    IExpr-comp-add↑-lemma : (m n : ℕ) (B : Fin (m + n) → ℕ)
                            (e₁ : IExpr m) (e₂ : IExpr n)
                            (ks : (a : Fin (m + n)) → IExpr (B a))
                          → PathP (λ i → IExpr (sum-split m n B (~ i)))
                                  (add↑ (IExpr-comp m (B ∘ injL m n) e₁ (ks ∘ injL m n))
                                        (IExpr-comp n (B ∘ injR m n) e₂ (ks ∘ injR m n)))
                                  (IExpr-comp (m + n) B (add↑ e₁ e₂) ks)
    IExpr-comp-add↑-lemma m n B e₁ e₂ ks =
      subst-filler IExpr (sym (sum-split m n B))
        (add↑ (IExpr-comp m (B ∘ injL m n) e₁ (ks ∘ injL m n))
              (IExpr-comp n (B ∘ injR m n) e₂ (ks ∘ injR m n)))

private
  -- All helpers for the id↑ case of IExpr-assoc, pulled out to top-level
  -- and wrapped in opaque blocks. They take B, C, ks, kss as parameters
  -- (matching the id↑ context). Each opaque definition prevents the
  -- normaliser from unfolding it when typechecking a later block.
  opaque
    -- The aligning family-path between (C fzero) and ⅀Assoc-C' 𝓝 1 B C,
    -- built via funExtDep using the ⅀Assoc-C'-id↑-eq lemma above.
    B-path-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
               → PathP (λ i → Fin (sym (+-zero (B fzero)) i) → ℕ)
                       (C fzero) (Universe.⅀Assoc-C' 𝓝 1 B C)
    B-path-id↑ B C = funExtDep λ {a₀} {a₁} a-path →
      let fst-eq : fst a₀ ≡ fst a₁
          fst-eq = sym (transport-Fin-fst (sym (+-zero (B fzero))) a₀)
                  ∙ cong fst (fromPathP a-path)
      in cong (C fzero) (Fin-fst-≡ fst-eq)
       ∙ sym (⅀Assoc-C'-id↑-eq B C a₁)

  -- Pointwise alignment for es-path-id↑'s funExtDep, pulled out so Agda
  -- can chunk the heavy proof; opaque to keep its body invisible.
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
      in subst (λ p → PathP (λ i → IExpr (p i))
                            (kss fzero a₀)
                            (kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁))
                                  (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) a₁))))
               (isSetℕ _ _ composed-path (λ i → B-path-id↑ B C i (a-path i)))
               composed

  opaque
    unfolding es-path-id↑-pointwise
    -- The aligning dependent-function-path between (kss fzero) and the
    -- ⅀Assoc-C'-indexed kss-application. Built by funExtDep on the
    -- pointwise alignment above.
    es-path-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                  (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
                → PathP (λ i → (a : Fin (sym (+-zero (B fzero)) i))
                              → IExpr (B-path-id↑ B C i a))
                        (kss fzero)
                        (λ ab → kss (fst (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab))
                                    (snd (equivFun (Universe.⟦⅀⟧ 𝓝 1 B) ab)))
    es-path-id↑ B C kss = funExtDep (es-path-id↑-pointwise B C kss)

  -- The two endpoints of the id↑-case assoc PathP, plus the helper Xinner.
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

  -- The bridge PathP from Xinner-id↑ to rhs-id↑ via IExpr-comp-PathP.
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

  -- LHS-to-Xinner via the outer subst-filler.
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

  -- Pure ℕ-equality witnessing the composed index path. Sealed independently
  -- so downstream consumers (e.g. IExpr-assoc-id↑) treat it as a black box.
  opaque
    chosen-path-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                    → sum (B fzero) (C fzero) + 0
                    ≡ sum (B fzero + 0) (Universe.⅀Assoc-C' 𝓝 1 B C)
    chosen-path-id↑ B C =
      +-zero (sum (B fzero) (C fzero))
      ∙ (λ i → sum (sym (+-zero (B fzero)) i) (B-path-id↑ B C i))

  -- Composed PathP from lhs-id↑ to rhs-id↑ via outer-id↑ then bridge-id↑.
  -- The declared type names chosen-path-id↑ (rather than inlining the hcomp);
  -- this lets IExpr-assoc-id↑'s subst match its motive by name without ever
  -- unfolding chosen-path-id↑. The unfolding cost is paid here, once.
  opaque
    unfolding chosen-path-id↑
    my-PathP-id↑ : (B : Fin 1 → ℕ) (C : (a : Fin 1) → Fin (B a) → ℕ)
                   (ks : (a : Fin 1) → IExpr (B a))
                   (kss : (a : Fin 1) (b : Fin (B a)) → IExpr (C a b))
                 → PathP (λ i → IExpr (chosen-path-id↑ B C i))
                         (lhs-id↑ B C ks kss) (rhs-id↑ B C ks kss)
    my-PathP-id↑ B C ks kss =
      compPathP' {B = IExpr} (outer-id↑ B C ks kss) (bridge-id↑ B C ks kss)

  -- The id↑ case of IExpr-assoc, assembled from the pieces above. Only
  -- lhs-id↑/rhs-id↑ need unfolding (so subst's motive matches the declared
  -- return type using IExpr-comp directly); my-PathP-id↑ and chosen-path-id↑
  -- are consumed by reference, not pattern-matched.
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
      subst (λ p → PathP (λ i → IExpr (p i)) (lhs-id↑ B C ks kss) (rhs-id↑ B C ks kss))
            (isSetℕ _ _ (chosen-path-id↑ B C) (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 1 B C)))
            (my-PathP-id↑ B C ks kss)

------------------------------------------------------------------------
-- IExpr-assoc-add↑ — the add↑ case of IExpr-assoc, assembled as
-- compPathP' of:
--   A: lhs-add↑ → add↑ Xinner-L Xinner-R       (symP subst-filler)
--   B: add↑ Xinner-L Xinner-R → add↑ recL recR (apply IH-L, IH-R)
--   C: add↑ recL recR → joint-form-add↑        (joint-form bridges + subst-filler)
--   D: joint-form-add↑ → rhs-add↑              (IExpr-comp-PathP)
-- Final isSetℕ swap from the composite ℕ-path to Inj 𝓝 (⅀Assoc≃ ...).
------------------------------------------------------------------------

private
  opaque
    Xinner-L-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                    (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                    (e₁ : IExpr m)
                    (ks : (a : Fin (m + n)) → IExpr (B a))
                    (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                  → IExpr (sum m ((λ a → sum (B a) (C a)) ∘ injL m n))
    Xinner-L-add↑ m n B C e₁ ks kss =
      IExpr-comp m ((λ a → sum (B a) (C a)) ∘ injL m n) e₁
                 (λ a → IExpr-comp (B (injL m n a)) (C (injL m n a))
                                    (ks (injL m n a)) (λ b → kss (injL m n a) b))

    Xinner-R-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                    (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                    (e₂ : IExpr n)
                    (ks : (a : Fin (m + n)) → IExpr (B a))
                    (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                  → IExpr (sum n ((λ a → sum (B a) (C a)) ∘ injR m n))
    Xinner-R-add↑ m n B C e₂ ks kss =
      IExpr-comp n ((λ a → sum (B a) (C a)) ∘ injR m n) e₂
                 (λ a → IExpr-comp (B (injR m n a)) (C (injR m n a))
                                    (ks (injR m n a)) (λ b → kss (injR m n a) b))

  opaque
    recL-IHend-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                      (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                      (e₁ : IExpr m)
                      (ks : (a : Fin (m + n)) → IExpr (B a))
                      (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                    → IExpr (sum (sum m (B ∘ injL m n))
                                  (Universe.⅀Assoc-C' 𝓝 m (B ∘ injL m n) (C ∘ injL m n)))
    recL-IHend-add↑ m n B C e₁ ks kss =
      IExpr-comp (sum m (B ∘ injL m n))
                 (Universe.⅀Assoc-C' 𝓝 m (B ∘ injL m n) (C ∘ injL m n))
                 (IExpr-comp m (B ∘ injL m n) e₁ (ks ∘ injL m n))
                 (λ ab → kss (injL m n (fst (sumFinFwd m (B ∘ injL m n) ab)))
                              (snd (sumFinFwd m (B ∘ injL m n) ab)))

    recR-IHend-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                      (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                      (e₂ : IExpr n)
                      (ks : (a : Fin (m + n)) → IExpr (B a))
                      (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                    → IExpr (sum (sum n (B ∘ injR m n))
                                  (Universe.⅀Assoc-C' 𝓝 n (B ∘ injR m n) (C ∘ injR m n)))
    recR-IHend-add↑ m n B C e₂ ks kss =
      IExpr-comp (sum n (B ∘ injR m n))
                 (Universe.⅀Assoc-C' 𝓝 n (B ∘ injR m n) (C ∘ injR m n))
                 (IExpr-comp n (B ∘ injR m n) e₂ (ks ∘ injR m n))
                 (λ ab → kss (injR m n (fst (sumFinFwd n (B ∘ injR m n) ab)))
                              (snd (sumFinFwd n (B ∘ injR m n) ab)))

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
                    → IExpr (sum (sum m (B ∘ injL m n) + sum n (B ∘ injR m n))
                                  (joint-C' m n B C))
    joint-form-add↑ m n B C e₁ e₂ ks kss =
      IExpr-comp (sum m (B ∘ injL m n) + sum n (B ∘ injR m n))
                 (joint-C' m n B C)
                 (add↑ (IExpr-comp m (B ∘ injL m n) e₁ (ks ∘ injL m n))
                       (IExpr-comp n (B ∘ injR m n) e₂ (ks ∘ injR m n)))
                 (joint-kss m n B C kss)

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

  opaque
    unfolding Xinner-L-add↑ Xinner-R-add↑ recL-IHend-add↑ recR-IHend-add↑
    step-B-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                  (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                  (e₁ : IExpr m) (e₂ : IExpr n)
                  (ks : (a : Fin (m + n)) → IExpr (B a))
                  (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                  (IH-L : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                (Universe.⅀Assoc≃ 𝓝 m (B ∘ injL m n)
                                                                       (C ∘ injL m n)) i))
                                (Xinner-L-add↑ m n B C e₁ ks kss)
                                (recL-IHend-add↑ m n B C e₁ ks kss))
                  (IH-R : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                (Universe.⅀Assoc≃ 𝓝 n (B ∘ injR m n)
                                                                       (C ∘ injR m n)) i))
                                (Xinner-R-add↑ m n B C e₂ ks kss)
                                (recR-IHend-add↑ m n B C e₂ ks kss))
                → PathP (λ i → IExpr ( Universe.Inj 𝓝
                                         (Universe.⅀Assoc≃ 𝓝 m (B ∘ injL m n)
                                                                (C ∘ injL m n)) i
                                       + Universe.Inj 𝓝
                                         (Universe.⅀Assoc≃ 𝓝 n (B ∘ injR m n)
                                                                (C ∘ injR m n)) i))
                        (add↑ (Xinner-L-add↑ m n B C e₁ ks kss)
                              (Xinner-R-add↑ m n B C e₂ ks kss))
                        (add↑ (recL-IHend-add↑ m n B C e₁ ks kss)
                              (recR-IHend-add↑ m n B C e₂ ks kss))
    step-B-add↑ m n B C e₁ e₂ ks kss IH-L IH-R i = add↑ (IH-L i) (IH-R i)

  opaque
    unfolding sum-split recL-IHend-add↑ recR-IHend-add↑ joint-form-add↑
              IExpr-comp-PathP
    step-C-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                  (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                  (e₁ : IExpr m) (e₂ : IExpr n)
                  (ks : (a : Fin (m + n)) → IExpr (B a))
                  (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                → PathP (λ i → IExpr (((λ j →
                            sum (sum m (B ∘ injL m n))
                                (λ kp → joint-C'-on-injL m n B C kp (~ j))
                          + sum (sum n (B ∘ injR m n))
                                (λ kp → joint-C'-on-injR m n B C kp (~ j)))
                       ∙ sym (sum-split (sum m (B ∘ injL m n))
                                        (sum n (B ∘ injR m n))
                                        (joint-C' m n B C))) i))
                        (add↑ (recL-IHend-add↑ m n B C e₁ ks kss)
                              (recR-IHend-add↑ m n B C e₂ ks kss))
                        (joint-form-add↑ m n B C e₁ e₂ ks kss)
    step-C-add↑ m n B C e₁ e₂ ks kss =
      let
        innerL = IExpr-comp m (B ∘ injL m n) e₁ (ks ∘ injL m n)
        innerR = IExpr-comp n (B ∘ injR m n) e₂ (ks ∘ injR m n)
        bridge-L : PathP (λ i → IExpr (sum (sum m (B ∘ injL m n))
                                             (λ kp → joint-C'-on-injL m n B C kp (~ i))))
                          (recL-IHend-add↑ m n B C e₁ ks kss)
                          (IExpr-comp (sum m (B ∘ injL m n))
                                      (λ kp → joint-C' m n B C
                                                 (injL (sum m (B ∘ injL m n))
                                                        (sum n (B ∘ injR m n)) kp))
                                      innerL
                                      (λ kp → joint-kss m n B C kss
                                                 (injL (sum m (B ∘ injL m n))
                                                        (sum n (B ∘ injR m n)) kp)))
        bridge-L = IExpr-comp-PathP refl
                                     (λ i kp → joint-C'-on-injL m n B C kp (~ i))
                                     {e = innerL} {e' = innerL} (λ _ → innerL)
                                     (λ i kp → joint-kss-on-injL m n B C kss kp (~ i))
        bridge-R : PathP (λ i → IExpr (sum (sum n (B ∘ injR m n))
                                             (λ kp → joint-C'-on-injR m n B C kp (~ i))))
                          (recR-IHend-add↑ m n B C e₂ ks kss)
                          (IExpr-comp (sum n (B ∘ injR m n))
                                      (λ kp → joint-C' m n B C
                                                 (injR (sum m (B ∘ injL m n))
                                                        (sum n (B ∘ injR m n)) kp))
                                      innerR
                                      (λ kp → joint-kss m n B C kss
                                                 (injR (sum m (B ∘ injL m n))
                                                        (sum n (B ∘ injR m n)) kp)))
        bridge-R = IExpr-comp-PathP refl
                                     (λ i kp → joint-C'-on-injR m n B C kp (~ i))
                                     {e = innerR} {e' = innerR} (λ _ → innerR)
                                     (λ i kp → joint-kss-on-injR m n B C kss kp (~ i))
        bridge-LR i = add↑ (bridge-L i) (bridge-R i)
        sub-step-2 = subst-filler IExpr
                       (sym (sum-split (sum m (B ∘ injL m n))
                                         (sum n (B ∘ injR m n))
                                         (joint-C' m n B C)))
                       (add↑ (IExpr-comp (sum m (B ∘ injL m n))
                                         (λ kp → joint-C' m n B C
                                                    (injL (sum m (B ∘ injL m n))
                                                           (sum n (B ∘ injR m n)) kp))
                                         innerL
                                         (λ kp → joint-kss m n B C kss
                                                    (injL (sum m (B ∘ injL m n))
                                                           (sum n (B ∘ injR m n)) kp)))
                             (IExpr-comp (sum n (B ∘ injR m n))
                                         (λ kp → joint-C' m n B C
                                                    (injR (sum m (B ∘ injL m n))
                                                           (sum n (B ∘ injR m n)) kp))
                                         innerR
                                         (λ kp → joint-kss m n B C kss
                                                    (injR (sum m (B ∘ injL m n))
                                                           (sum n (B ∘ injR m n)) kp))))
      in compPathP' {B = IExpr} bridge-LR sub-step-2

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

  -- chosen-path-add↑ is purely an ℕ-equality; it does not need any of the
  -- step-* helpers unfolded. Sealed in its own opaque block so downstream
  -- consumers (e.g. IExpr-assoc-add↑) treat it as a black box.
  opaque
    chosen-path-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                     → sum (m + n) (λ a → sum (B a) (C a))
                     ≡ sum (sum (m + n) B) (Universe.⅀Assoc-C' 𝓝 (m + n) B C)
    chosen-path-add↑ m n B C =
        sum-split m n (λ a → sum (B a) (C a))
      ∙ (λ i → ( Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 m (B ∘ injL m n) (C ∘ injL m n)) i
               + Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 n (B ∘ injR m n) (C ∘ injR m n)) i))
      ∙ ((λ j →
            sum (sum m (B ∘ injL m n))
                (λ kp → joint-C'-on-injL m n B C kp (~ j))
          + sum (sum n (B ∘ injR m n))
                (λ kp → joint-C'-on-injR m n B C kp (~ j)))
        ∙ sym (sum-split (sum m (B ∘ injL m n)) (sum n (B ∘ injR m n))
                          (joint-C' m n B C)))
      ∙ (λ i → sum (sym (sum-split m n B) i) (symP (B-path-add↑ m n B C) i))

  opaque
    unfolding chosen-path-add↑ step-A-add↑ step-B-add↑ step-C-add↑ step-D-add↑

    composite-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                     (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                     (e₁ : IExpr m) (e₂ : IExpr n)
                     (ks : (a : Fin (m + n)) → IExpr (B a))
                     (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                     (IH-L : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                    (Universe.⅀Assoc≃ 𝓝 m (B ∘ injL m n)
                                                                           (C ∘ injL m n)) i))
                                    (Xinner-L-add↑ m n B C e₁ ks kss)
                                    (recL-IHend-add↑ m n B C e₁ ks kss))
                     (IH-R : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                    (Universe.⅀Assoc≃ 𝓝 n (B ∘ injR m n)
                                                                           (C ∘ injR m n)) i))
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

  -- IExpr-assoc-add↑ only needs lhs-add↑/rhs-add↑ unfolded so the subst's
  -- motive matches the declared return type. composite-add↑ is passed as a
  -- value (its type matches the motive by name); chosen-path-add↑ is referenced
  -- only inside isSetℕ where syntactic equality suffices.
  opaque
    unfolding lhs-add↑ rhs-add↑

    IExpr-assoc-add↑ : (m n : ℕ) (B : Fin (m + n) → ℕ)
                       (C : (a : Fin (m + n)) → Fin (B a) → ℕ)
                       (e₁ : IExpr m) (e₂ : IExpr n)
                       (ks : (a : Fin (m + n)) → IExpr (B a))
                       (kss : (a : Fin (m + n)) (b : Fin (B a)) → IExpr (C a b))
                       (IH-L : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                      (Universe.⅀Assoc≃ 𝓝 m (B ∘ injL m n)
                                                                             (C ∘ injL m n)) i))
                                      (Xinner-L-add↑ m n B C e₁ ks kss)
                                      (recL-IHend-add↑ m n B C e₁ ks kss))
                       (IH-R : PathP (λ i → IExpr (Universe.Inj 𝓝
                                                      (Universe.⅀Assoc≃ 𝓝 n (B ∘ injR m n)
                                                                             (C ∘ injR m n)) i))
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
      subst (λ p → PathP (λ i → IExpr (p i))
                          (lhs-add↑ m n B C e₁ e₂ ks kss)
                          (rhs-add↑ m n B C e₁ e₂ ks kss))
            (isSetℕ _ _ (chosen-path-add↑ m n B C)
                        (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 (m + n) B C)))
            (composite-add↑ m n B C e₁ e₂ ks kss IH-L IH-R)

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
    subst (λ p → PathP (λ i → IExpr (p i)) (val↑ n) (val↑ n))
          (isSetℕ _ _ refl (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 0 B C)))
          refl
  IExpr-assoc .1 B C id↑ ks kss = IExpr-assoc-id↑ B C ks kss
  IExpr-assoc .(m + n) B C (add↑ {m} {n} e₁ e₂) ks kss =
    IExpr-assoc-add↑ m n B C e₁ e₂ ks kss
      (IExpr-assoc m (B ∘ injL m n) (C ∘ injL m n) e₁
                   (ks ∘ injL m n) (λ a → kss (injL m n a)))
      (IExpr-assoc n (B ∘ injR m n) (C ∘ injR m n) e₂
                   (ks ∘ injR m n) (λ a → kss (injR m n a)))

-- The IExpr operad, assembled as a NonSymmOperad (= Operad 𝓝).
IExprOperad : NonSymmOperad IExpr
Operad.isSetK IExprOperad = isSetIExpr
Operad.id     IExprOperad = id↑
Operad.compₒ  IExprOperad = IExpr-comp
Operad.idl    IExprOperad = IExpr-idl
Operad.idr    IExprOperad = IExpr-idr
Operad.assoc  IExprOperad = IExpr-assoc
