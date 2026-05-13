{-# OPTIONS --cubical #-}
module HoTTOperads.Prelude.Nat where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence using (ua ; pathToEquiv ; ua-pathToEquiv)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Data.Nat public hiding (elim)
open import Cubical.Data.Nat.Properties public using (+-zero ; +-suc ; +-comm ; +-assoc)
open import Cubical.Data.Nat.Order using
  ( _≤_ ; _<_ ; suc-≤-suc ; zero-≤ ; isProp≤ ; pred-≤-pred ; ¬-<-zero ; <-k+
  ; ¬m<m ; ≤<-trans ; ¬m+n<m )
open import Cubical.Data.Fin public using (Fin ; fzero ; fsuc)
open import Cubical.Data.Fin.Properties using
  ( Fin-fst-≡ ; isSetFin ; Fin+≅Fin⊎Fin ; _≤?_ ; o<m→o<m+n ; ∸-<-lemma
  ; m+n∸n=m ; ∸-lemma )
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-fst ; Σ≡Prop)
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sum.Properties using (⊎-equiv ; Σ⊎≃)
open import Cubical.Data.Empty using () renaming (rec to ⊥-rec)
open import Cubical.Data.Empty.Properties using (uninhabEquiv)
open import Cubical.Data.Unit using (Unit ; tt)

private
  variable
    ℓ : Level
    n m : ℕ

------------------------------------------------------------------------
-- Finite summation.
------------------------------------------------------------------------

sum : (n : ℕ) → (Fin n → ℕ) → ℕ
sum zero    ns = 0
sum (suc n) ns = ns fzero + sum n (λ i → ns (fsuc i))

opaque
  sum-idr : ∀ n → sum n (λ _ → 1) ≡ n
  sum-idr zero    = refl
  sum-idr (suc n) = cong suc (sum-idr n)

¬Fin0 : ¬ Fin 0
¬Fin0 (_ , k<0) = ¬-<-zero k<0

------------------------------------------------------------------------
-- A canonical equivalence (Unit ⊎ Fin n) ≃ Fin (suc n).
------------------------------------------------------------------------

private
  ι-Fin : Unit ⊎ Fin n → Fin (suc n)
  ι-Fin (inl tt) = fzero
  ι-Fin (inr k)  = fsuc k

  ι-Fin⁻¹ : Fin (suc n) → Unit ⊎ Fin n
  ι-Fin⁻¹ (zero  , _) = inl tt
  ι-Fin⁻¹ (suc k , p) = inr (k , pred-≤-pred p)

  ι-rinv : (i : Fin (suc n)) → ι-Fin (ι-Fin⁻¹ i) ≡ i
  ι-rinv (zero  , _) = Fin-fst-≡ refl
  ι-rinv (suc k , _) = Fin-fst-≡ refl

  ι-linv : (x : Unit ⊎ Fin n) → ι-Fin⁻¹ (ι-Fin x) ≡ x
  ι-linv (inl tt) = refl
  ι-linv (inr (k , p)) = cong inr (Fin-fst-≡ refl)

FinSuc≃ : (n : ℕ) → (Unit ⊎ Fin n) ≃ Fin (suc n)
FinSuc≃ _ = isoToEquiv (iso ι-Fin ι-Fin⁻¹ ι-rinv ι-linv)

ΣFinSuc≃ : (n : ℕ) (f : Fin (suc n) → Type ℓ)
         → Σ (Fin (suc n)) f ≃ (f fzero ⊎ Σ (Fin n) (f ∘ fsuc))
ΣFinSuc≃ {ℓ} n f =
  Σ (Fin (suc n)) f
    ≃⟨ invEquiv (Σ-cong-equiv-fst (FinSuc≃ n)) ⟩
  Σ (Unit ⊎ Fin n) (f ∘ ι-Fin)
    ≃⟨ Σ⊎≃ ⟩
  Σ Unit (λ _ → f fzero) ⊎ Σ (Fin n) (λ k → f (fsuc k))
    ≃⟨ ⊎-equiv ΣUnit-≃ (idEquiv _) ⟩
  f fzero ⊎ Σ (Fin n) (f ∘ fsuc) ■
  where
    ΣUnit-≃ : ∀ {ℓ'} {A : Type ℓ'} → Σ Unit (λ _ → A) ≃ A
    ΣUnit-≃ = isoToEquiv (iso snd (λ a → tt , a) (λ _ → refl) (λ _ → refl))

------------------------------------------------------------------------
-- The canonical equivalence Fin (sum n ns) ≃ Σ[ i ∈ Fin n ] Fin (ns i),
-- expressed as an iso with explicit forward and inverse, so that
--   invEq (sumFinEquiv n ns) ≡ sumFinBwd n ns           definitionally
--   equivFun (sumFinEquiv n ns) ≡ sumFinFwd n ns        definitionally
-- and in particular fst (sumFinBwd n ns (i , j)) reduces to a clean
-- arithmetic expression in `sum-prefix n ns i + fst j`.
------------------------------------------------------------------------

-- The prefix sum of `ns` over the Fin elements strictly below `i`.
-- Only the ℕ-component of i is consulted; the bound proof is irrelevant.
sum-prefix : (n : ℕ) (ns : Fin n → ℕ) → Fin n → ℕ
sum-prefix zero    ns (_     , p) = ⊥-rec (¬-<-zero p)
sum-prefix (suc n) ns (zero  , _) = 0
sum-prefix (suc n) ns (suc k , p) =
  ns fzero + sum-prefix n (ns ∘ fsuc) (k , pred-≤-pred p)

-- Forward direction: case-split on whether the flat index falls in
-- the first block (`ns fzero`) or the tail.
sumFinFwd : (n : ℕ) (ns : Fin n → ℕ)
          → Fin (sum n ns) → Σ[ i ∈ Fin n ] Fin (ns i)
sumFinFwd zero    ns (_ , p) = ⊥-rec (¬-<-zero p)
sumFinFwd (suc n) ns (k , p) with k ≤? ns fzero
... | inl k<m = fzero , (k , k<m)
... | inr m≤k =
  let rec = sumFinFwd n (ns ∘ fsuc)
                       (k ∸ ns fzero , ∸-<-lemma (ns fzero) (sum n (ns ∘ fsuc)) k p m≤k)
  in fsuc (fst rec) , snd rec

-- Bound for the inverse direction, factored as a lemma on ℕ-arguments so
-- there is no need to inspect the proof component of the input Fin n.
sum-prefix-bound : (n : ℕ) (ns : Fin n → ℕ) (i : Fin n)
                 → (j : ℕ) → j < ns i
                 → sum-prefix n ns i + j < sum n ns
sum-prefix-bound zero    ns (_     , p) _ _    = ⊥-rec (¬-<-zero p)
sum-prefix-bound (suc n) ns (zero  , p) j j<ns =
  o<m→o<m+n (ns fzero) (sum n (ns ∘ fsuc)) j
            (subst (j <_) (cong ns (Fin-fst-≡ refl)) j<ns)
sum-prefix-bound (suc n) ns (suc k , p) j j<ns =
  subst (_< ns fzero + sum n (ns ∘ fsuc))
        (+-assoc (ns fzero) (sum-prefix n (ns ∘ fsuc) (k , pred-≤-pred p)) j)
        (<-k+ {k = ns fzero}
              (sum-prefix-bound n (ns ∘ fsuc) (k , pred-≤-pred p) j
                                 (subst (j <_) (cong ns (Fin-fst-≡ refl)) j<ns)))

-- Inverse direction: lexicographic linearization.
-- fst is *definitionally* `sum-prefix n ns i + fst j`.
sumFinBwd : (n : ℕ) (ns : Fin n → ℕ)
          → Σ[ i ∈ Fin n ] Fin (ns i) → Fin (sum n ns)
sumFinBwd n ns (i , (j , jp)) =
  sum-prefix n ns i + j , sum-prefix-bound n ns i j jp

opaque
  -- Witness-irrelevance lemma: sum-prefix only depends on fst.
  sum-prefix-irrel : (n : ℕ) (ns : Fin n → ℕ) (i : ℕ) (p q : i < n)
                   → sum-prefix n ns (i , p) ≡ sum-prefix n ns (i , q)
  sum-prefix-irrel n ns i p q = cong (sum-prefix n ns) (Fin-fst-≡ refl)

  -- A tiny arithmetic lemma used in the right-inverse: cancellation of `m`
  -- prepended via +-assoc; (m + s) ∸ m ≡ s.
  +-∸-cancel : (m s : ℕ) → (m + s) ∸ m ≡ s
  +-∸-cancel m s = cong (_∸ m) (+-comm m s) ∙ m+n∸n=m m s

------------------------------------------------------------------------
-- Inversion proofs for sumFinIso.
------------------------------------------------------------------------

opaque
  -- A handy two-level Σ-path constructor when both Fin layers are propositional.
  Fin-Σ-fst-≡ : {n : ℕ} {ns : Fin n → ℕ}
              → {i₁ i₂ : Fin n} → (p : i₁ ≡ i₂)
              → {j₁ : Fin (ns i₁)} {j₂ : Fin (ns i₂)}
              → fst j₁ ≡ fst j₂
              → _≡_ {A = Σ (Fin n) (λ i → Fin (ns i))} (i₁ , j₁) (i₂ , j₂)
  Fin-Σ-fst-≡ {ns = ns} {i₁ = i₁} {i₂ = i₂} p {j₁ = j₁} {j₂ = j₂} q =
    ΣPathP ( p
           , toPathP (Σ≡Prop (λ _ → isProp≤)
                              (transport-Fin-fst (cong ns p) j₁ ∙ q)) )
    where
      -- forward declaration used below
      transport-Fin-fst : {a b : ℕ} (e : a ≡ b) (k : Fin a)
                        → fst (transport (cong Fin e) k) ≡ fst k
      transport-Fin-fst {a} = J (λ b e → (k : Fin a) → fst (transport (cong Fin e) k) ≡ fst k)
                                (λ k → cong fst (transportRefl k))

opaque
  -- The right inverse: sumFinFwd ∘ sumFinBwd = id.
  -- Strategy: case-split as `sumFinFwd` does; absorb proof-irrelevant
  -- components via `Fin-Σ-fst-≡`.
  sumFinFwd-Bwd : (n : ℕ) (ns : Fin n → ℕ) (x : Σ[ i ∈ Fin n ] Fin (ns i))
                → sumFinFwd n ns (sumFinBwd n ns x) ≡ x
  sumFinFwd-Bwd zero    ns ((_ , p) , _) = ⊥-rec (¬-<-zero p)
  sumFinFwd-Bwd (suc n) ns ((zero , p) , (j , jp)) with j ≤? ns fzero
  ... | inl j<m =
    Fin-Σ-fst-≡ {ns = ns} (Fin-fst-≡ {i = fzero} {j = (zero , p)} refl) refl
  ... | inr m≤j =
    ⊥-rec (¬m<m (≤<-trans m≤j (subst (j <_) (cong ns (Fin-fst-≡ refl)) jp)))
  sumFinFwd-Bwd (suc n) ns ((suc k , p) , (j , jp))
    with (ns fzero + sum-prefix n (ns ∘ fsuc) (k , pred-≤-pred p) + j) ≤? ns fzero
  ... | inl absurd =
    ⊥-rec (¬m+n<m {m = ns fzero}
                   {n = sum-prefix n (ns ∘ fsuc) (k , pred-≤-pred p) + j}
                   (subst (_< ns fzero)
                          (sym (+-assoc (ns fzero) _ j))
                          absurd))
  ... | inr _ =
    let
      S    = sum-prefix n (ns ∘ fsuc) (k , pred-≤-pred p)
      -- jp bridged to the recursive type Fin ((ns ∘ fsuc) (k, pred-≤-pred p)).
      jp'  = subst (j <_) (cong ns (Fin-fst-≡ {i = (suc k , p)}
                                                {j = fsuc (k , pred-≤-pred p)}
                                                refl)) jp
      -- (1) The recursive call argument equals sumFinBwd's output (modulo prop bound).
      rec-arg-eq :
          _≡_ {A = Σ ℕ (_< sum n (ns ∘ fsuc))}
              ((ns fzero + S + j) ∸ ns fzero
              , _)
              (sumFinBwd n (ns ∘ fsuc) ((k , pred-≤-pred p) , (j , jp')))
      rec-arg-eq = Σ≡Prop (λ _ → isProp≤)
                           ( cong (_∸ ns fzero) (sym (+-assoc (ns fzero) S j))
                           ∙ +-∸-cancel (ns fzero) (S + j) )
      -- (2) Apply IH on n; the recursive sumFinFwd then yields ((k, pred-≤-pred p), (j, jp')).
      IH  : sumFinFwd n (ns ∘ fsuc)
              (sumFinBwd n (ns ∘ fsuc) ((k , pred-≤-pred p) , (j , jp')))
          ≡ ((k , pred-≤-pred p) , (j , jp'))
      IH  = sumFinFwd-Bwd n (ns ∘ fsuc) ((k , pred-≤-pred p) , (j , jp'))
      -- (3) Chain: outer wraps in fsuc; bridge the witness on both layers.
      rec-call-eq : sumFinFwd n (ns ∘ fsuc) ((ns fzero + S + j) ∸ ns fzero , _)
                  ≡ ((k , pred-≤-pred p) , (j , jp'))
      rec-call-eq = cong (sumFinFwd n (ns ∘ fsuc)) rec-arg-eq ∙ IH
      bridge : (fsuc (k , pred-≤-pred p) , (j , jp')) ≡ ((suc k , p) , (j , jp))
      bridge = Fin-Σ-fst-≡ {ns = ns}
                            (Fin-fst-≡ {i = fsuc (k , pred-≤-pred p)} {j = (suc k , p)} refl)
                            refl
    in (λ i → fsuc (fst (rec-call-eq i)) , snd (rec-call-eq i)) ∙ bridge

  -- The left inverse: sumFinBwd ∘ sumFinFwd = id.
  sumFinBwd-Fwd : (n : ℕ) (ns : Fin n → ℕ) (k : Fin (sum n ns))
                → sumFinBwd n ns (sumFinFwd n ns k) ≡ k
  sumFinBwd-Fwd zero    ns (_ , p) = ⊥-rec (¬-<-zero p)
  sumFinBwd-Fwd (suc n) ns (k , p) with k ≤? ns fzero
  ... | inl k<m =
    -- sumFinFwd ... = (fzero, (k, k<m)).
    -- sumFinBwd ... ((fzero, (k, k<m))) = (sum-prefix (suc n) ns fzero + k, _) = (0 + k, _) = (k, _).
    Σ≡Prop (λ _ → isProp≤) refl
  ... | inr m≤k =
    let
      rec-input = (k ∸ ns fzero , ∸-<-lemma (ns fzero) (sum n (ns ∘ fsuc)) k p m≤k)
      rec       = sumFinFwd n (ns ∘ fsuc) rec-input
      -- IH: sumFinBwd n (ns ∘ fsuc) rec ≡ rec-input.
      IH  : sumFinBwd n (ns ∘ fsuc) rec ≡ rec-input
      IH  = sumFinBwd-Fwd n (ns ∘ fsuc) rec-input
      -- sumFinBwd (suc n) ns (fsuc (fst rec), snd rec)
      --   = (sum-prefix (suc n) ns (fsuc (fst rec)) + fst (snd rec), _)
      -- where sum-prefix (suc n) ns (fsuc (fst rec)) ≡ ns fzero + sum-prefix n (ns ∘ fsuc) (fst rec)
      -- (this requires witness-irrelevance bridge).
      sp-eq : sum-prefix (suc n) ns (fsuc (fst rec))
            ≡ ns fzero + sum-prefix n (ns ∘ fsuc) (fst rec)
      sp-eq = cong (ns fzero +_)
                   (sum-prefix-irrel n (ns ∘ fsuc) (fst (fst rec)) _ _)
    in Σ≡Prop (λ _ → isProp≤)
              ( cong (_+ fst (snd rec)) sp-eq
              ∙ sym (+-assoc (ns fzero) (sum-prefix n (ns ∘ fsuc) (fst rec)) (fst (snd rec)))
              ∙ cong (ns fzero +_) (cong fst IH)
              ∙ ∸-lemma m≤k )

sumFinIso : (n : ℕ) (ns : Fin n → ℕ)
          → Iso (Fin (sum n ns)) (Σ[ i ∈ Fin n ] Fin (ns i))
Iso.fun      (sumFinIso n ns) = sumFinFwd n ns
Iso.inv      (sumFinIso n ns) = sumFinBwd n ns
Iso.rightInv (sumFinIso n ns) = sumFinFwd-Bwd n ns
Iso.leftInv  (sumFinIso n ns) = sumFinBwd-Fwd n ns

sumFinEquiv : (n : ℕ) (ns : Fin n → ℕ)
            → Fin (sum n ns) ≃ (Σ[ i ∈ Fin n ] Fin (ns i))
sumFinEquiv n ns = isoToEquiv (sumFinIso n ns)

-- Sanity checks that the intended reductions hold definitionally.
private
  module _ (n : ℕ) (ns : Fin n → ℕ) (i : Fin n) (j : Fin (ns i)) where
    _ : equivFun (sumFinEquiv n ns) ≡ sumFinFwd n ns
    _ = refl
    _ : invEq (sumFinEquiv n ns) ≡ sumFinBwd n ns
    _ = refl
    _ : fst (sumFinBwd n ns (i , j)) ≡ sum-prefix n ns i + fst j
    _ = refl

------------------------------------------------------------------------
-- Witness-free prefix sum and splitting lemmas, used in the Fubini
-- identity for `⅀Assoc-preserves-fst`.
------------------------------------------------------------------------

-- Prefix sum over the first k indices, taking k : ℕ rather than Fin n
-- (so no bound proof and no witness-irrelevance issues during recursion).
-- Note: ordering of clauses matters — index-zero takes priority so that
-- `sum-prefix-ℕ n f 0` reduces definitionally to `0` regardless of `n`.
sum-prefix-ℕ : (n : ℕ) (ns : Fin n → ℕ) → ℕ → ℕ
sum-prefix-ℕ _       _  zero    = 0
sum-prefix-ℕ zero    _  (suc _) = 0
sum-prefix-ℕ (suc n) ns (suc k) = ns fzero + sum-prefix-ℕ n (ns ∘ fsuc) k

opaque
  -- Bridge to the Fin-indexed prefix sum.
  sum-prefix-≡ : ∀ n ns (i : Fin n) → sum-prefix n ns i ≡ sum-prefix-ℕ n ns (fst i)
  sum-prefix-≡ zero    ns (_     , p) = ⊥-rec (¬-<-zero p)
  sum-prefix-≡ (suc n) ns (zero  , _) = refl
  sum-prefix-≡ (suc n) ns (suc k , p) = cong (ns fzero +_)
                                              (sum-prefix-≡ n (ns ∘ fsuc) (k , pred-≤-pred p))

  -- Functoriality of sum-prefix-ℕ on the function argument.
  sum-prefix-ℕ-cong : (n : ℕ) {f g : Fin n → ℕ}
                    → ((i : Fin n) → f i ≡ g i)
                    → (k : ℕ) → sum-prefix-ℕ n f k ≡ sum-prefix-ℕ n g k
  sum-prefix-ℕ-cong _       _ zero    = refl
  sum-prefix-ℕ-cong zero    _ (suc _) = refl
  sum-prefix-ℕ-cong (suc n) h (suc k) =
    cong₂ _+_ (h fzero) (sum-prefix-ℕ-cong n (λ i → h (fsuc i)) k)

  -- Functoriality of sum on the function argument.
  sum-cong : (n : ℕ) {f g : Fin n → ℕ}
           → ((i : Fin n) → f i ≡ g i)
           → sum n f ≡ sum n g
  sum-cong zero    _ = refl
  sum-cong (suc n) h = cong₂ _+_ (h fzero) (sum-cong n (λ i → h (fsuc i)))

  -- The full sum is sum-prefix-ℕ at index n.
  sum≡sum-prefix-ℕ : ∀ n g → sum n g ≡ sum-prefix-ℕ n g n
  sum≡sum-prefix-ℕ zero    _ = refl
  sum≡sum-prefix-ℕ (suc n) g = cong (g fzero +_) (sum≡sum-prefix-ℕ n (g ∘ fsuc))

-- Natural embeddings into Fin (m + n).
inj-l-+ : (m n : ℕ) → Fin m → Fin (m + n)
inj-l-+ m n (k , klt) = k , o<m→o<m+n m n k klt

inj-r-+ : (m n : ℕ) → Fin n → Fin (m + n)
inj-r-+ m n (k , klt) = m + k , <-k+ {k = m} klt

opaque
  -- Restricting sum-prefix-ℕ to the first-block (inl) range.
  sum-prefix-ℕ-l : (m n : ℕ) (f : Fin (m + n) → ℕ) (k : ℕ) → k ≤ m
                → sum-prefix-ℕ (m + n) f k
                ≡ sum-prefix-ℕ m (λ i → f (inj-l-+ m n i)) k
  sum-prefix-ℕ-l m       n f zero    _   = refl
  sum-prefix-ℕ-l zero    n f (suc k) k≤m = ⊥-rec (¬-<-zero k≤m)
  sum-prefix-ℕ-l (suc m) n f (suc k) k≤m =
    cong₂ _+_ (cong f (Fin-fst-≡ refl))
               ( sum-prefix-ℕ-l m n (f ∘ fsuc) k (pred-≤-pred k≤m)
               ∙ sum-prefix-ℕ-cong m (λ _ → cong f (Fin-fst-≡ refl)) k )

  -- Computing sum-prefix-ℕ at indices ≥ m in terms of full first-block + tail prefix.
  sum-prefix-ℕ-r : (m n : ℕ) (f : Fin (m + n) → ℕ) (k : ℕ) → k ≤ n
                → sum-prefix-ℕ (m + n) f (m + k)
                ≡ sum m (λ i → f (inj-l-+ m n i))
                + sum-prefix-ℕ n (λ i → f (inj-r-+ m n i)) k
  sum-prefix-ℕ-r zero    n f k k≤n =
    sum-prefix-ℕ-cong n (λ _ → cong f (Fin-fst-≡ refl)) k
  sum-prefix-ℕ-r (suc m) n f k k≤n =
      cong (f fzero +_) (sum-prefix-ℕ-r m n (f ∘ fsuc) k k≤n)
    ∙ +-assoc (f fzero)
              (sum m (λ i → (f ∘ fsuc) (inj-l-+ m n i)))
              (sum-prefix-ℕ n (λ i → (f ∘ fsuc) (inj-r-+ m n i)) k)
    ∙ cong₂ _+_
          (cong₂ _+_
            (cong f (Fin-fst-≡ refl))
            (sum-cong m (λ _ → cong f (Fin-fst-≡ refl))))
          (sum-prefix-ℕ-cong n (λ _ → cong f (Fin-fst-≡ refl)) k)

------------------------------------------------------------------------
-- Key abstract lemma: an equivalence e : Fin n ≃ Fin m whose forward
-- function preserves the underlying ℕ-index is propositionally equal to
-- pathToEquiv (cong Fin p) for any path p : n ≡ m.
------------------------------------------------------------------------

opaque
  transport-Fin-fst : {n m : ℕ} (p : n ≡ m) (k : Fin n)
                    → fst (transport (cong Fin p) k) ≡ fst k
  transport-Fin-fst {n} = J (λ m p → (k : Fin n) → fst (transport (cong Fin p) k) ≡ fst k)
                            (λ k → cong fst (transportRefl k))

  equivFin-by-fst : {n m : ℕ} (e : Fin n ≃ Fin m) (p : n ≡ m)
                  → ((k : Fin n) → fst (equivFun e k) ≡ fst k)
                  → e ≡ pathToEquiv (cong Fin p)
  equivFin-by-fst e p hyp =
    equivEq (funExt λ k → Fin-fst-≡ (hyp k ∙ sym (transport-Fin-fst p k)))

------------------------------------------------------------------------
-- Impossibility eliminators for the `with k ≤? bound` pattern.
-- The structure is always: `with k ≤? bound`; one branch is the real
-- proof and the other branch derives `bound ≤ k` together with `k < bound`,
-- which is absurd. These helpers name that absurdity once.
------------------------------------------------------------------------

absurd-≤? : {X : Type ℓ} {k bound : ℕ} → bound ≤ k → k < bound → X
absurd-≤? B≤k k<B = ⊥-rec (¬m<m (≤<-trans B≤k k<B))

absurd-+-≤? : {X : Type ℓ} {b k : ℕ} → (b + k) < b → X
absurd-+-≤? {b = b} {k = k} = ⊥-rec ∘ ¬m+n<m {m = b} {n = k}

------------------------------------------------------------------------
-- Building a path B i ≡ B j over Fin n from a fst-path. The Fin-fst-≡
-- + cong combination is one of the most-repeated idioms in the operadic
-- proofs (~40 occurrences in IExpr alone).
------------------------------------------------------------------------

cong-Fin-fst : ∀ {ℓ'} {n : ℕ} {B : Fin n → Type ℓ'}
               {i j : Fin n} → fst i ≡ fst j → B i ≡ B j
cong-Fin-fst {B = B} p = cong B (Fin-fst-≡ p)
