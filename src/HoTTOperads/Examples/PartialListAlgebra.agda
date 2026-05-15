{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Examples.PartialListAlgebra
--
-- The function `fill : PartialList A n → (Fin n → List A) → List A` and
-- its packaging as an algebra of `PartialListOperad A` on `List A` — i.e.,
-- an operad morphism `PartialListOperad A ⇒ Endo 𝓝 (List A)`. Filling each
-- hole of a partial list with a list yields a concrete list.
--
-- Formalises from the paper:
--   Proposition 4.3 (Section 4, Planar Operads) — `fill⇒`.
-- (`fill` itself is the construction the paper names `fill`.)
-- ============================================================================
module HoTTOperads.Examples.PartialListAlgebra where

open import Cubical.Foundations.Prelude hiding (fill)
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (invEq ; equivFun)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Properties using (+-assoc)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Fin.Properties using (isContrFin1 ; Fin-fst-≡)
import Cubical.Data.List as L
open L using (List ; [] ; _∷_)
open import Cubical.Data.List.Properties using (++-unit-r ; ++-assoc ; isOfHLevelList)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Unit using (tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Instances.Nat
  using (𝓝 ; sum ; sumFinFwd ; inj-l-+ ; inj-r-+)
open import HoTTOperads.Prelude.Nat using (sumFinBwd ; sum-prefix)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Morphism
open import HoTTOperads.Operad.Endo
open import HoTTOperads.Operad.Specialised.NonSymm using (NonSymmOperad)
open import HoTTOperads.Examples.PartialList
  using (PartialList ; poke ; pl-comp ; PartialListOperad ; _++_)

private
  variable
    ℓ : Level

module _ {A : Type ℓ} (isSetA : isSet A) where
  private
    isSetListA : isSet (List A)
    isSetListA = isOfHLevelList 0 isSetA

  -- Proposition 4.3 (Section 4, Planar Operads).
  -- Fill the n holes of a `PartialList A n` with `n` lists from `(Fin n → List A)`.
  -- The data constructors recurse in the obvious way; `poke ps` plugs the
  -- hole at the head with `ks fzero` and continues with the suffix.
  fill : (n : ℕ) → PartialList A n → (Fin n → List A) → List A
  fill .0       PartialList.[]                ks = []
  fill n       (a PartialList.∷ ps)           ks = a ∷ fill n ps ks
  fill .(suc _) (poke {n = m'} ps)            ks = ks fzero L.++ fill m' ps (ks ∘ fsuc)

  ------------------------------------------------------------------------
  -- Distributivity of `fill` over `PartialList ++` — a `List A`-codomain
  -- analogue of `pl-comp-++` (Examples/PartialList.agda). Since `List A`
  -- has no arity index, the equality is a plain `_≡_` (no PathP needed).
  -- The bookkeeping mirrors `pl-comp-++` exactly: family-reindex bridges
  -- between `ks ∘ fsuc ∘ inj-l-+ m n` and `ks ∘ inj-l-+ (suc m) n ∘ fsuc`
  -- (and similarly on the right) collapse to `cong ks (Fin-fst-≡ refl)`.
  ------------------------------------------------------------------------
  private opaque
    fill-++ : (m n : ℕ) (xs : PartialList A m) (ys : PartialList A n)
              (ks : Fin (m + n) → List A)
            → fill (m + n) (xs ++ ys) ks
            ≡ fill m xs (ks ∘ inj-l-+ m n) L.++ fill n ys (ks ∘ inj-r-+ m n)
    -- []-case: m = 0; `0 + n` reduces to `n`. LHS = fill n ys ks; RHS =
    -- [] L.++ fill n ys (ks ∘ inj-r-+ 0 n) = fill n ys (ks ∘ inj-r-+ 0 n).
    -- Bridge: `inj-r-+ 0 n (k, klt)` has the same fst as `(k, klt)`.
    fill-++ .0 n PartialList.[] ys ks =
      cong (fill n ys) (funExt λ kp → cong ks (Fin-fst-≡ refl))
    -- ∷-case: both sides reduce to `a ∷ …`; apply IH.
    fill-++ m n (a PartialList.∷ xs') ys ks =
      cong (a ∷_) (fill-++ m n xs' ys ks)
    -- poke-case (m = suc m_inner): LHS unfolds via `++` and `fill _ (poke …)`
    -- to `ks fzero L.++ fill (m_inner + n) (xs' ++ ys) (ks ∘ fsuc)`. IH on
    -- `xs'` splits the tail; reassociate via `++-assoc` and bridge the
    -- family-reindex differences via `cong ks (Fin-fst-≡ refl)`.
    fill-++ .(suc _) n (poke {n = m_inner} xs') ys ks =
        cong (ks fzero L.++_) (fill-++ m_inner n xs' ys (ks ∘ fsuc))
      ∙ sym (++-assoc (ks fzero)
                       (fill m_inner xs' (ks ∘ fsuc ∘ inj-l-+ m_inner n))
                       (fill n ys (ks ∘ fsuc ∘ inj-r-+ m_inner n)))
      ∙ cong₂ L._++_
          (cong₂ L._++_
            (cong ks (Fin-fst-≡ {i = fzero {k = m_inner + n}}
                                 {j = inj-l-+ (suc m_inner) n fzero} refl))
            (cong (fill m_inner xs')
                  (funExt λ a → cong ks (Fin-fst-≡
                    {i = fsuc (inj-l-+ m_inner n a)}
                    {j = inj-l-+ (suc m_inner) n (fsuc a)} refl))))
          (cong (fill n ys)
                (funExt λ a → cong ks (Fin-fst-≡
                  {i = fsuc (inj-r-+ m_inner n a)}
                  {j = inj-r-+ (suc m_inner) n a} refl)))

  ------------------------------------------------------------------------
  -- Bridge lemmas between `sumFinBwd` on `(fzero, _)`/`(fsuc a, _)` and
  -- the `inj-l-+`/`inj-r-+` reindexes used by `pl-comp-++` and `fill-++`.
  -- Both follow from `Fin-fst-≡` on the underlying ℕ-projection: the LHS
  -- fst reduces by `sum-prefix (suc m') ns fzero = 0` (resp. by the suc-
  -- clause of `sum-prefix`), and the RHS fst is read off the definitions
  -- of `inj-l-+` / `inj-r-+`.
  ------------------------------------------------------------------------
  private opaque
    invEq-sumFin-fzero :
      (m' : ℕ) (ns : Fin (suc m') → ℕ) (b : Fin (ns fzero))
      → sumFinBwd (suc m') ns (fzero , b)
      ≡ inj-l-+ (ns fzero) (sum m' (ns ∘ fsuc)) b
    invEq-sumFin-fzero m' ns b = Fin-fst-≡ refl

    invEq-sumFin-fsuc :
      (m' : ℕ) (ns : Fin (suc m') → ℕ) (a : Fin m') (b : Fin (ns (fsuc a)))
      → sumFinBwd (suc m') ns (fsuc a , b)
      ≡ inj-r-+ (ns fzero) (sum m' (ns ∘ fsuc)) (sumFinBwd m' (ns ∘ fsuc) (a , b))
    invEq-sumFin-fsuc m' ns a b =
      -- The LHS fst unfolds via the suc-clause of `sum-prefix` to
      -- `(ns fzero + sum-prefix m' (ns ∘ fsuc) (fst a, pred-≤-pred …)) + fst b`,
      -- where the bound proof differs from `a`'s by `pred-≤-pred (suc-≤-suc …)`.
      -- Step 1 collapses that bound difference (same fst); step 2 reassociates.
      Fin-fst-≡
        (cong (λ x → (ns fzero + x) + fst b)
              (cong (sum-prefix m' (ns ∘ fsuc))
                    (Fin-fst-≡ {i = _} {j = a} refl))
         ∙ sym (+-assoc (ns fzero) (sum-prefix m' (ns ∘ fsuc) a) (fst b)))

  -- Proposition 4.3 (the algebra packaging).
  -- The morphism `fill⇒ : PartialListOperad A ⇒ Endo 𝓝 (List A)`.
  fill⇒ : PartialListOperad A isSetA ⇒ Endo 𝓝 isSetListA
  _⇒_.⟪_⟫    fill⇒ n p ks       = fill n p ks
  _⇒_.on-id  fill⇒              = on-id-proof
    where
      open Universe 𝓝
      -- Both sides take `ks : Fin 1 → List A` and return a list. On the
      -- LHS, `fill 1 (poke []) ks` reduces to `ks fzero ++ []`, while
      -- `Endo-id ks` returns `ks (invEq ⟦𝜏⟧ tt)`. The two agree by
      -- `++-unit-r` and `Fin 1`-contractibility.
      on-id-proof : fill 1 (poke PartialList.[]) ≡
                    Operad.id (Endo 𝓝 isSetListA)
      on-id-proof =
        funExt λ ks →
            ++-unit-r (ks fzero)
          ∙ cong ks (snd isContrFin1 fzero)
          ∙ cong ks (sym (snd isContrFin1 (invEq ⟦𝜏⟧ tt)))
  _⇒_.on-comp fill⇒ n ns k ks = on-comp-proof n ns k ks
    where
      open Universe 𝓝
      -- The [] and (∷) cases of the induction on `k` reduce definitionally.
      -- The (poke) case combines `fill-++` (above) with a recursive call
      -- (structurally smaller `k'`), bridged via `invEq-sumFin-fzero` /
      -- `-fsuc` to convert `inj-l-+`/`inj-r-+` reindexes into the form
      -- `Endo-comp` produces (`invEq (sumFinEquiv (suc m') ns) (·, ·)`
      -- on `(fzero, _)` / `(fsuc a, _)` slices).
      on-comp-proof :
        (n : Universe.Code 𝓝) (ns : Universe.El 𝓝 n → Universe.Code 𝓝)
        (k : PartialList A n)
        (ks : (a : Universe.El 𝓝 n) → PartialList A (ns a))
        → fill (⅀ n ns) (pl-comp A n ns k ks)
        ≡ Operad.compₒ (Endo 𝓝 isSetListA) n ns (fill n k)
                        (λ a → fill (ns a) (ks a))
      on-comp-proof n ns PartialList.[]                ks =
        funExt λ _ → refl
      on-comp-proof n ns (a PartialList.∷ k')          ks =
        funExt λ xs → cong (a ∷_) (funExt⁻ (on-comp-proof n ns k' ks) xs)
      on-comp-proof .(suc _) ns (poke {n = m'} k')     ks =
        funExt λ xs →
            -- LHS unfolds (via `pl-comp` poke clause and `fill-++`) to a
            -- `L._++_` of two `fill`s whose `ks`-arguments are
            -- `xs ∘ inj-l-+ …` and `xs ∘ inj-r-+ …`.
            fill-++ (ns fzero) (sum m' (ns ∘ fsuc))
                    (ks fzero) (pl-comp A m' (ns ∘ fsuc) k' (ks ∘ fsuc)) xs
          ∙ cong₂ L._++_
              -- LEFT factor: replace `xs ∘ inj-l-+ …` by
              -- `λ b → xs (sumFinBwd (suc m') ns (fzero, b))` via the
              -- `fzero` bridge.
              (cong (fill (ns fzero) (ks fzero))
                    (funExt λ b → cong xs (sym (invEq-sumFin-fzero m' ns b))))
              -- RIGHT factor: apply the IH at `m'` (structurally smaller
              -- `k'`), then bridge the resulting `inj-r-+ … ∘ sumFinBwd m' …`
              -- to `sumFinBwd (suc m') ns (fsuc a, _)` via the `fsuc` bridge.
              ( funExt⁻ (on-comp-proof m' (ns ∘ fsuc) k' (ks ∘ fsuc))
                         (xs ∘ inj-r-+ (ns fzero) (sum m' (ns ∘ fsuc)))
              ∙ cong (fill m' k')
                     (funExt λ a →
                        cong (fill (ns (fsuc a)) (ks (fsuc a)))
                             (funExt λ b →
                                cong xs (sym (invEq-sumFin-fsuc m' ns a b)))))
