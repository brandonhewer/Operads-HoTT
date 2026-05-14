{-# OPTIONS --cubical #-}
module HoTTOperads.Examples.PartialList where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Properties using (+-zero ; +-assoc ; +-comm)
open import Cubical.Data.Nat.Order using (<-k+ ; ¬m<m ; ≤<-trans ; ¬m+n<m)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Fin.Properties using
  ( Fin-fst-≡ ; o<m→o<m+n ; _≤?_ ; m+n∸n=m )
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥ ; isProp⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit ; isPropUnit)
open import Cubical.Data.Sigma using (_×_ ; _,_)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Instances.Nat using
  ( 𝓝 ; sum ; inj-l-+ ; inj-r-+ ; sumFinFwd ; ⅀Assoc-C'-on-inl ; ⅀Assoc-C'-on-inr )
open import HoTTOperads.Prelude.Path using (isSet→subst-PathP)
open import HoTTOperads.Prelude.Nat using (absurd-≤? ; absurd-+-≤?)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Specialised.NonSymm using (NonSymmOperad)

private
  variable
    ℓ : Level

-- Partial lists indexed by the number of holes (`poke`s).
data PartialList (A : Type ℓ) : ℕ → Type ℓ where
  []   : PartialList A 0
  _∷_  : ∀ {n} → A → PartialList A n → PartialList A n
  poke : ∀ {n} → PartialList A n → PartialList A (suc n)

-- Concatenation: holes add up.
_++_ : ∀ {A : Type ℓ} {m n} → PartialList A m → PartialList A n → PartialList A (m + n)
[]        ++ ys = ys
(x ∷ xs)  ++ ys = x ∷ (xs ++ ys)
poke xs   ++ ys = poke (xs ++ ys)

------------------------------------------------------------------------
-- isSet for PartialList, by the standard encode-decode argument.  Mirrors
-- `Cubical.Data.List.Properties.ListPath` / `isOfHLevelList`, extended
-- with the third constructor `poke`.  The index `n` is implicit; Agda's
-- unifier eliminates the index-conflicting rows ([] / poke and poke / [])
-- on its own.
------------------------------------------------------------------------
private
  module PartialListPath {A : Type ℓ} where
    Cover : ∀ {n} → PartialList A n → PartialList A n → Type ℓ
    Cover []        []        = Lift Unit
    Cover []        (_ ∷ _)   = Lift ⊥
    Cover (_ ∷ _)   []        = Lift ⊥
    Cover (x ∷ xs)  (y ∷ ys)  = (x ≡ y) × Cover xs ys
    Cover (_ ∷ _)   (poke _)  = Lift ⊥
    Cover (poke _)  (_ ∷ _)   = Lift ⊥
    Cover (poke xs) (poke ys) = Cover xs ys

    reflCode : ∀ {n} (xs : PartialList A n) → Cover xs xs
    reflCode []        = lift tt
    reflCode (_ ∷ xs)  = refl , reflCode xs
    reflCode (poke xs) = reflCode xs

    encode : ∀ {n} (xs ys : PartialList A n) → xs ≡ ys → Cover xs ys
    encode xs _ = J (λ ys _ → Cover xs ys) (reflCode xs)

    encodeRefl : ∀ {n} (xs : PartialList A n) → encode xs xs refl ≡ reflCode xs
    encodeRefl xs = JRefl (λ ys _ → Cover xs ys) (reflCode xs)

    decode : ∀ {n} (xs ys : PartialList A n) → Cover xs ys → xs ≡ ys
    decode []        []        _        = refl
    decode []        (_ ∷ _)   (lift ())
    decode (_ ∷ _)   []        (lift ())
    decode (x ∷ xs)  (y ∷ ys)  (p , c)  = cong₂ _∷_ p (decode xs ys c)
    decode (_ ∷ _)   (poke _)  (lift ())
    decode (poke _)  (_ ∷ _)   (lift ())
    decode (poke xs) (poke ys) c        = cong poke (decode xs ys c)

    decodeRefl : ∀ {n} (xs : PartialList A n) → decode xs xs (reflCode xs) ≡ refl
    decodeRefl []        = refl
    decodeRefl (x ∷ xs)  = cong (cong₂ _∷_ refl) (decodeRefl xs)
    decodeRefl (poke xs) = cong (cong poke) (decodeRefl xs)

    decodeEncode : ∀ {n} (xs ys : PartialList A n) (p : xs ≡ ys)
                 → decode xs ys (encode xs ys p) ≡ p
    decodeEncode xs _ =
      J (λ ys p → decode xs ys (encode xs ys p) ≡ p)
        (cong (decode xs xs) (encodeRefl xs) ∙ decodeRefl xs)

    isOfHLevelCover : (n : HLevel) → isOfHLevel (suc (suc n)) A
                    → ∀ {k} (xs ys : PartialList A k)
                    → isOfHLevel (suc n) (Cover xs ys)
    isOfHLevelCover n p []        []        =
      isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isPropUnit)
    isOfHLevelCover n p []        (_ ∷ _)   =
      isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
    isOfHLevelCover n p (_ ∷ _)   []        =
      isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
    isOfHLevelCover n p (x ∷ xs)  (y ∷ ys)  =
      isOfHLevelΣ (suc n) (p x y) (λ _ → isOfHLevelCover n p xs ys)
    isOfHLevelCover n p (_ ∷ _)   (poke _)  =
      isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
    isOfHLevelCover n p (poke _)  (_ ∷ _)   =
      isOfHLevelLift (suc n) (isProp→isOfHLevelSuc n isProp⊥)
    isOfHLevelCover n p (poke xs) (poke ys) =
      isOfHLevelCover n p xs ys

opaque
  isOfHLevelPartialList : (n : HLevel) {A : Type ℓ}
                        → isOfHLevel (suc (suc n)) A
                        → (k : ℕ) → isOfHLevel (suc (suc n)) (PartialList A k)
  isOfHLevelPartialList n ofLevel k xs ys =
    isOfHLevelRetract (suc n)
      (PartialListPath.encode xs ys)
      (PartialListPath.decode xs ys)
      (PartialListPath.decodeEncode xs ys)
      (PartialListPath.isOfHLevelCover n ofLevel xs ys)

  isSetPartialList : {A : Type ℓ} → isSet A → (n : ℕ) → isSet (PartialList A n)
  isSetPartialList = isOfHLevelPartialList 0

------------------------------------------------------------------------
-- A small helper: swap the ℕ-path indexing a PartialList-valued PathP.
-- Since ℕ is an h-set, the choice of underlying ℕ-equality is unique
-- up to propositional equality, so we may freely transport between any
-- two such paths.
------------------------------------------------------------------------
private
  swap-PathP : ∀ {A : Type ℓ} {m n}
               {x : PartialList A m} {y : PartialList A n}
               (p q : m ≡ n)
             → PathP (λ i → PartialList A (p i)) x y
             → PathP (λ i → PartialList A (q i)) x y
  swap-PathP {A = A} p q path = isSet→subst-PathP isSetℕ {B = PartialList A} p q path

------------------------------------------------------------------------
-- The sum over Fin (m + n) splits into a prefix and suffix sum, in the
-- style of IExpr.agda.
------------------------------------------------------------------------
private
  -- sum-split kept transparent: pl-comp-++ below pattern-matches on it
  -- (the base-case PathP type involves sum-split zero q ns ix, which must reduce).
  sum-split : (m n : ℕ) (B : Fin (m + n) → ℕ)
            → sum (m + n) B ≡ sum m (B ∘ inj-l-+ m n) + sum n (B ∘ inj-r-+ m n)
  sum-split zero    n B =
    cong (sum n) (funExt λ kp → cong B (Fin-fst-≡ refl))
  sum-split (suc m) n B =
      B fzero + sum (m + n) (B ∘ fsuc)
        ≡⟨ cong (B fzero +_) (sum-split m n (B ∘ fsuc)) ⟩
      B fzero + (sum m (B ∘ fsuc ∘ inj-l-+ m n) + sum n (B ∘ fsuc ∘ inj-r-+ m n))
        ≡⟨ +-assoc (B fzero) _ _ ⟩
      (B fzero + sum m (B ∘ fsuc ∘ inj-l-+ m n)) + sum n (B ∘ fsuc ∘ inj-r-+ m n)
        ≡⟨ cong₂ _+_ left-eq right-eq ⟩
      sum (suc m) (B ∘ inj-l-+ (suc m) n) + sum n (B ∘ inj-r-+ (suc m) n) ∎
    where
      left-eq : B fzero + sum m (B ∘ fsuc ∘ inj-l-+ m n)
              ≡ B (inj-l-+ (suc m) n fzero) + sum m (B ∘ inj-l-+ (suc m) n ∘ fsuc)
      left-eq = cong₂ _+_ (cong B (Fin-fst-≡ refl))
                         (cong (sum m) (funExt λ kp → cong B (Fin-fst-≡ refl)))
      right-eq : sum n (B ∘ fsuc ∘ inj-r-+ m n) ≡ sum n (B ∘ inj-r-+ (suc m) n)
      right-eq = cong (sum n) (funExt λ kp → cong B (Fin-fst-≡ refl))

------------------------------------------------------------------------
-- Right unit and associativity of concatenation.
------------------------------------------------------------------------
private
  opaque
    ++-unit-r : ∀ {A : Type ℓ} {m} (xs : PartialList A m)
              → PathP (λ i → PartialList A (+-zero m i)) (xs ++ []) xs
    ++-unit-r []        = refl
    ++-unit-r (x ∷ xs)  = λ i → x ∷ ++-unit-r xs i
    ++-unit-r (poke xs) = λ i → poke (++-unit-r xs i)

    ++-assoc-PL : ∀ {A : Type ℓ} {p q r}
                  (xs : PartialList A p) (ys : PartialList A q) (zs : PartialList A r)
                → PathP (λ i → PartialList A (sym (+-assoc p q r) i))
                        ((xs ++ ys) ++ zs) (xs ++ (ys ++ zs))
    ++-assoc-PL []        ys zs = refl
    ++-assoc-PL (x ∷ xs)  ys zs = λ i → x ∷ ++-assoc-PL xs ys zs i
    ++-assoc-PL (poke xs) ys zs = λ i → poke (++-assoc-PL xs ys zs i)

------------------------------------------------------------------------
-- IExpr-style operadic composition for partial lists, by induction on
-- the outer list. No internal subst is required since `_∷_` keeps the
-- arity and `poke` adds exactly one hole.
------------------------------------------------------------------------
pl-comp : (A : Type ℓ) (n : ℕ) (ns : Fin n → ℕ)
        → PartialList A n
        → ((a : Fin n) → PartialList A (ns a))
        → PartialList A (sum n ns)
pl-comp A .0        ns []               xss = []
pl-comp A n         ns (x ∷ ys)         xss = x ∷ pl-comp A n ns ys xss
pl-comp A .(suc _)  ns (poke {n = m'} ys) xss =
  xss fzero ++ pl-comp A m' (ns ∘ fsuc) ys (xss ∘ fsuc)

------------------------------------------------------------------------
-- Left identity: pl-comp A 1 (λ _ → m) (poke []) (λ _ → k) reduces
-- definitionally to k ++ [].
------------------------------------------------------------------------
opaque
  pl-idl : (A : Type ℓ) (m : ℕ) (k : PartialList A m)
         → PathP (λ i → PartialList A (Universe.Inj 𝓝 (Universe.⅀Idl≃ 𝓝 m) i))
                 (pl-comp A 1 (λ _ → m) (poke []) (λ _ → k)) k
  pl-idl A m k = swap-PathP (+-zero m) _ (++-unit-r k)

------------------------------------------------------------------------
-- Right identity. PathP over the canonical ℕ-path sum-idr m, then swap
-- to the operad's expected path via swap-PathP.
------------------------------------------------------------------------
private
  opaque
    -- The canonical ℕ-path sum n (λ _ → 1) ≡ n.
    sum-idr-path : ∀ n → sum n (λ _ → 1) ≡ n
    sum-idr-path zero    = refl
    sum-idr-path (suc n) = cong suc (sum-idr-path n)

    pl-idr-aux : ∀ {A : Type ℓ} (m : ℕ) (k : PartialList A m)
               → PathP (λ i → PartialList A (sum-idr-path m i))
                       (pl-comp A m (λ _ → 1) k (λ _ → poke [])) k
    pl-idr-aux .0        []                  = refl
    pl-idr-aux m         (x ∷ ys)            = λ i → x ∷ pl-idr-aux m ys i
    pl-idr-aux .(suc _)  (poke {n = m'} ys)  = λ i → poke (pl-idr-aux m' ys i)

opaque
  pl-idr : (A : Type ℓ) (m : ℕ) (k : PartialList A m)
         → PathP (λ i → PartialList A (Universe.Inj 𝓝 (Universe.⅀Idr≃ 𝓝 m) i))
                 (pl-comp A m (λ _ → 1) k (λ _ → poke [])) k
  pl-idr A m k = swap-PathP (sum-idr-path m) _ (pl-idr-aux m k)

------------------------------------------------------------------------
-- Distributivity of pl-comp over _++_.
------------------------------------------------------------------------
private
 opaque
  pl-comp-++ : ∀ {A : Type ℓ} (p q : ℕ)
               (xs : PartialList A p) (ys : PartialList A q)
               (ns : Fin (p + q) → ℕ)
               (vs : (a : Fin (p + q)) → PartialList A (ns a))
             → PathP (λ i → PartialList A (sum-split p q ns i))
                     (pl-comp A (p + q) ns (xs ++ ys) vs)
                     (pl-comp A p (ns ∘ inj-l-+ p q) xs (vs ∘ inj-l-+ p q)
                      ++ pl-comp A q (ns ∘ inj-r-+ p q) ys (vs ∘ inj-r-+ p q))
  -- Base case: xs = [] (so p = 0).
  pl-comp-++ zero q [] ys ns vs ix =
    pl-comp _ q
            (λ kp → ns (Fin-fst-≡ {i = kp} {j = inj-r-+ zero q kp} refl ix))
            ys
            (λ a  → vs (Fin-fst-≡ {i = a}  {j = inj-r-+ zero q a}  refl ix))
  -- Cons case: x ∷ propagates trivially.
  pl-comp-++ p q (x ∷ xs) ys ns vs = λ ix → x ∷ pl-comp-++ p q xs ys ns vs ix
  -- Poke case (p = suc p'): the heavy case.
  pl-comp-++ {A = A} (suc p') q (poke {n = p'} xs) ys ns vs =
    swap-PathP _ _ composite
    where
      ns'  : Fin (p' + q) → ℕ
      ns'  = ns ∘ fsuc
      vs'  : (a : Fin (p' + q)) → PartialList A (ns' a)
      vs'  = vs ∘ fsuc

      ih : PathP (λ ix → PartialList A (sum-split p' q ns' ix))
                 (pl-comp A (p' + q) ns' (xs ++ ys) vs')
                 (pl-comp A p' (ns' ∘ inj-l-+ p' q) xs (vs' ∘ inj-l-+ p' q)
                  ++ pl-comp A q (ns' ∘ inj-r-+ p' q) ys (vs' ∘ inj-r-+ p' q))
      ih = pl-comp-++ p' q xs ys ns' vs'

      L-reix-ns : (a : Fin p')
                → (ns' ∘ inj-l-+ p' q) a ≡ (ns ∘ inj-l-+ (suc p') q ∘ fsuc) a
      L-reix-ns a = cong ns (Fin-fst-≡ {i = fsuc (inj-l-+ p' q a)}
                                        {j = inj-l-+ (suc p') q (fsuc a)} refl)

      L-step :
        PathP (λ ix → PartialList A (sum p' (λ a → L-reix-ns a ix)))
              (pl-comp A p' (ns' ∘ inj-l-+ p' q) xs (vs' ∘ inj-l-+ p' q))
              (pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                            (vs ∘ inj-l-+ (suc p') q ∘ fsuc))
      L-step ix = pl-comp A p' (λ a → L-reix-ns a ix) xs
                          (λ a → vs (Fin-fst-≡ {i = fsuc (inj-l-+ p' q a)}
                                                {j = inj-l-+ (suc p') q (fsuc a)}
                                                refl ix))

      R-reix-ns : (a : Fin q)
                → (ns' ∘ inj-r-+ p' q) a ≡ (ns ∘ inj-r-+ (suc p') q) a
      R-reix-ns a = cong ns (Fin-fst-≡ {i = fsuc (inj-r-+ p' q a)}
                                        {j = inj-r-+ (suc p') q a} refl)

      R-step :
        PathP (λ ix → PartialList A (sum q (λ a → R-reix-ns a ix)))
              (pl-comp A q (ns' ∘ inj-r-+ p' q) ys (vs' ∘ inj-r-+ p' q))
              (pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys (vs ∘ inj-r-+ (suc p') q))
      R-step ix = pl-comp A q (λ a → R-reix-ns a ix) ys
                          (λ a → vs (Fin-fst-≡ {i = fsuc (inj-r-+ p' q a)}
                                                {j = inj-r-+ (suc p') q a}
                                                refl ix))

      head-step :
        PathP (λ ix → PartialList A
                       (ns (Fin-fst-≡ {i = fzero {k = p' + q}}
                                      {j = inj-l-+ (suc p') q (fzero {k = p'})}
                                      refl ix)))
              (vs fzero) (vs (inj-l-+ (suc p') q fzero))
      head-step ix = vs (Fin-fst-≡ {i = fzero {k = p' + q}}
                                    {j = inj-l-+ (suc p') q (fzero {k = p'})}
                                    refl ix)

      stage12 :
        PathP (λ ix → PartialList A (ns fzero + sum-split p' q ns' ix))
              (vs fzero ++ pl-comp A (p' + q) ns' (xs ++ ys) vs')
              (vs fzero ++ (pl-comp A p' (ns' ∘ inj-l-+ p' q) xs (vs' ∘ inj-l-+ p' q)
                            ++ pl-comp A q (ns' ∘ inj-r-+ p' q) ys (vs' ∘ inj-r-+ p' q)))
      stage12 ix = vs fzero ++ ih ix

      stage3 :
        PathP (λ ix → PartialList A
                       (ns fzero + (sum p' (λ a → L-reix-ns a ix)
                                    + sum q (λ a → R-reix-ns a ix))))
              (vs fzero ++ (pl-comp A p' (ns' ∘ inj-l-+ p' q) xs (vs' ∘ inj-l-+ p' q)
                            ++ pl-comp A q (ns' ∘ inj-r-+ p' q) ys (vs' ∘ inj-r-+ p' q)))
              (vs fzero ++ (pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                          (vs ∘ inj-l-+ (suc p') q ∘ fsuc)
                            ++ pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                          (vs ∘ inj-r-+ (suc p') q)))
      stage3 ix = vs fzero ++ (L-step ix ++ R-step ix)

      stage4 :
        PathP (λ ix → PartialList A
                       (ns (Fin-fst-≡ {i = fzero {k = p' + q}}
                                       {j = inj-l-+ (suc p') q (fzero {k = p'})}
                                       refl ix)
                        + (sum p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc)
                           + sum q (ns ∘ inj-r-+ (suc p') q))))
              (vs fzero ++ (pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                          (vs ∘ inj-l-+ (suc p') q ∘ fsuc)
                            ++ pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                          (vs ∘ inj-r-+ (suc p') q)))
              (vs (inj-l-+ (suc p') q fzero)
                ++ (pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                 (vs ∘ inj-l-+ (suc p') q ∘ fsuc)
                    ++ pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                   (vs ∘ inj-r-+ (suc p') q)))
      stage4 ix = head-step ix
                  ++ (pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                   (vs ∘ inj-l-+ (suc p') q ∘ fsuc)
                      ++ pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                     (vs ∘ inj-r-+ (suc p') q))

      stage5 :
        PathP (λ ix → PartialList A
                       (sym (sym (+-assoc (ns (inj-l-+ (suc p') q fzero))
                                           (sum p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc))
                                           (sum q (ns ∘ inj-r-+ (suc p') q)))) ix))
              (vs (inj-l-+ (suc p') q fzero)
                ++ (pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                 (vs ∘ inj-l-+ (suc p') q ∘ fsuc)
                    ++ pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                   (vs ∘ inj-r-+ (suc p') q)))
              ((vs (inj-l-+ (suc p') q fzero)
                 ++ pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                  (vs ∘ inj-l-+ (suc p') q ∘ fsuc))
                ++ pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                (vs ∘ inj-r-+ (suc p') q))
      stage5 = symP (++-assoc-PL (vs (inj-l-+ (suc p') q fzero))
                                  (pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                                (vs ∘ inj-l-+ (suc p') q ∘ fsuc))
                                  (pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                                (vs ∘ inj-r-+ (suc p') q)))

      composite :
        PathP (λ ix → PartialList A
                       (((λ ix → ns fzero + sum-split p' q ns' ix)
                          ∙ (λ ix → ns fzero + (sum p' (λ a → L-reix-ns a ix)
                                                 + sum q (λ a → R-reix-ns a ix)))
                          ∙ (λ ix → ns (Fin-fst-≡ {i = fzero {k = p' + q}}
                                                   {j = inj-l-+ (suc p') q (fzero {k = p'})}
                                                   refl ix)
                                     + (sum p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc)
                                        + sum q (ns ∘ inj-r-+ (suc p') q)))
                          ∙ sym (sym (+-assoc (ns (inj-l-+ (suc p') q fzero))
                                               (sum p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc))
                                               (sum q (ns ∘ inj-r-+ (suc p') q))))) ix))
              (vs fzero ++ pl-comp A (p' + q) ns' (xs ++ ys) vs')
              ((vs (inj-l-+ (suc p') q fzero)
                ++ pl-comp A p' (ns ∘ inj-l-+ (suc p') q ∘ fsuc) xs
                                 (vs ∘ inj-l-+ (suc p') q ∘ fsuc))
                ++ pl-comp A q (ns ∘ inj-r-+ (suc p') q) ys
                                (vs ∘ inj-r-+ (suc p') q))
      composite = compPathP' {B = PartialList A} stage12
                  (compPathP' {B = PartialList A} stage3
                  (compPathP' {B = PartialList A} stage4 stage5))

------------------------------------------------------------------------
-- Value-level bridge lemmas: relate kss-suc on inj-l-+ / inj-r-+
-- back to kss / (kss ∘ fsuc). The universe-level ⅀Assoc-C'-on-inl /
-- ⅀Assoc-C'-on-inr lemmas are re-used from Universe.Instances.Nat;
-- they are opaque there, so we unfold them inside this block to allow
-- the with-clauses below to reduce.
------------------------------------------------------------------------
private
 opaque
  unfolding ⅀Assoc-C'-on-inl ⅀Assoc-C'-on-inr
  kss-bridge-L :
    ∀ {A : Type ℓ} (A' : ℕ) (B : Fin (suc A') → ℕ)
      (C : (a : Fin (suc A')) → Fin (B a) → ℕ)
      (kss : (a : Fin (suc A')) (b : Fin (B a)) → PartialList A (C a b))
      (kp : Fin (B fzero))
    → PathP (λ i → PartialList A (⅀Assoc-C'-on-inl A' B C kp i))
            (kss (fst (sumFinFwd (suc A') B (inj-l-+ (B fzero) (sum A' (B ∘ fsuc)) kp)))
                 (snd (sumFinFwd (suc A') B (inj-l-+ (B fzero) (sum A' (B ∘ fsuc)) kp))))
            (kss fzero kp)
  kss-bridge-L A' B C kss (k , k<m) with k ≤? B fzero
  ... | inl _   = λ i → kss fzero (Fin-fst-≡ {i = (k , _)} {j = (k , k<m)} refl i)
  ... | inr B≤k = absurd-≤? B≤k k<m

  kss-bridge-R :
    ∀ {A : Type ℓ} (A' : ℕ) (B : Fin (suc A') → ℕ)
      (C : (a : Fin (suc A')) → Fin (B a) → ℕ)
      (kss : (a : Fin (suc A')) (b : Fin (B a)) → PartialList A (C a b))
      (kp : Fin (sum A' (B ∘ fsuc)))
    → PathP (λ i → PartialList A (⅀Assoc-C'-on-inr A' B C kp i))
            (kss (fst (sumFinFwd (suc A') B (inj-r-+ (B fzero) (sum A' (B ∘ fsuc)) kp)))
                 (snd (sumFinFwd (suc A') B (inj-r-+ (B fzero) (sum A' (B ∘ fsuc)) kp))))
            (kss (fsuc (fst (sumFinFwd A' (B ∘ fsuc) kp)))
                 (snd (sumFinFwd A' (B ∘ fsuc) kp)))
  kss-bridge-R A' B C kss (k , klt) with (B fzero + k) ≤? B fzero
  ... | inl B+k<B  = absurd-+-≤? {b = B fzero} {k = k} B+k<B
  ... | inr B≤B+k  =
    λ i → kss (fsuc (fst (sumFinFwd A' (B ∘ fsuc)
                            (Fin-fst-≡ {i = (B fzero + k ∸ B fzero , _)} {j = (k , klt)}
                              ((cong (_∸ B fzero) (+-comm (B fzero) k))
                               ∙ m+n∸n=m (B fzero) k) i))))
              (snd (sumFinFwd A' (B ∘ fsuc)
                      (Fin-fst-≡ {i = (B fzero + k ∸ B fzero , _)} {j = (k , klt)}
                        ((cong (_∸ B fzero) (+-comm (B fzero) k))
                         ∙ m+n∸n=m (B fzero) k) i)))

------------------------------------------------------------------------
-- Associativity.  Direct induction on k, using pl-comp-++ + the bridges
-- in the poke case.  We work over a convenient ℕ-path and swap to the
-- operad's target via swap-PathP.
------------------------------------------------------------------------
private
 opaque
  pl-assoc-aux : ∀ {A : Type ℓ}
                 (m : ℕ) (ms : Fin m → ℕ)
                 (mss : (a : Fin m) → Fin (ms a) → ℕ)
                 (k : PartialList A m)
                 (ks : (a : Fin m) → PartialList A (ms a))
                 (kss : (a : Fin m) (b : Fin (ms a)) → PartialList A (mss a b))
               → PathP (λ i → PartialList A (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 m ms mss) i))
                       (pl-comp A m (λ a → sum (ms a) (mss a)) k
                                (λ a → pl-comp A (ms a) (mss a) (ks a) (kss a)))
                       (pl-comp A (sum m ms) (Universe.⅀Assoc-C' 𝓝 m ms mss)
                                (pl-comp A m ms k ks)
                                (λ ab → kss _ _))
  pl-assoc-aux .0 ms mss [] ks kss =
    swap-PathP refl _ refl
  pl-assoc-aux m ms mss (x ∷ ys) ks kss =
    λ i → x ∷ pl-assoc-aux m ms mss ys ks kss i
  pl-assoc-aux {A = A} .(suc _) ms mss (poke {n = m'} ys) ks kss =
    swap-PathP _ _ composite
    where
      ms' : Fin m' → ℕ
      ms'   = ms  ∘ fsuc
      mss' : (a : Fin m') → Fin (ms' a) → ℕ
      mss'  = mss ∘ fsuc
      ks' : (a : Fin m') → PartialList A (ms' a)
      ks'   = ks  ∘ fsuc
      kss' : (a : Fin m') (b : Fin (ms' a)) → PartialList A (mss' a b)
      kss'  = kss ∘ fsuc

      C-suc : Fin (sum (suc m') ms) → ℕ
      C-suc = Universe.⅀Assoc-C' 𝓝 (suc m') ms mss

      kss-suc : (a : Fin (sum (suc m') ms)) → PartialList A (C-suc a)
      kss-suc ab = kss _ _

      ih : PathP (λ i → PartialList A
                          (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 m' ms' mss') i))
                 (pl-comp A m' (λ a → sum (ms' a) (mss' a)) ys
                          (λ a → pl-comp A (ms' a) (mss' a) (ks' a) (kss' a)))
                 (pl-comp A (sum m' ms') (Universe.⅀Assoc-C' 𝓝 m' ms' mss')
                          (pl-comp A m' ms' ys ks')
                          (λ ab → kss' _ _))
      ih = pl-assoc-aux m' ms' mss' ys ks' kss'

      inner : PartialList A (sum (ms fzero) (mss fzero))
      inner = pl-comp A (ms fzero) (mss fzero) (ks fzero) (kss fzero)

      outer-LHS-rec :
        PartialList A (sum m' (λ a → sum (ms' a) (mss' a)))
      outer-LHS-rec = pl-comp A m' (λ a → sum (ms' a) (mss' a)) ys
                              (λ a → pl-comp A (ms' a) (mss' a) (ks' a) (kss' a))

      outer-RHS-rec :
        PartialList A (sum (sum m' ms') (Universe.⅀Assoc-C' 𝓝 m' ms' mss'))
      outer-RHS-rec = pl-comp A (sum m' ms') (Universe.⅀Assoc-C' 𝓝 m' ms' mss')
                              (pl-comp A m' ms' ys ks') (λ ab → kss' _ _)

      -- Step α: apply the IH to the outer ++.
      stage-α : PathP (λ i → PartialList A
                              (sum (ms fzero) (mss fzero)
                               + Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 m' ms' mss') i))
                     (inner ++ outer-LHS-rec)
                     (inner ++ outer-RHS-rec)
      stage-α i = inner ++ ih i

      -- Reindex paths on C-suc components, supplied by ⅀Assoc-C'-on-inl/inr.
      L-reix : (kp : Fin (ms fzero))
             → (C-suc ∘ inj-l-+ (ms fzero) (sum m' ms')) kp ≡ mss fzero kp
      L-reix kp = ⅀Assoc-C'-on-inl m' ms mss kp

      R-reix : (kp : Fin (sum m' ms'))
             → (C-suc ∘ inj-r-+ (ms fzero) (sum m' ms')) kp
               ≡ Universe.⅀Assoc-C' 𝓝 m' ms' mss' kp
      R-reix kp = ⅀Assoc-C'-on-inr m' ms mss kp

      L-vs-bridge :
        (kp : Fin (ms fzero))
        → PathP (λ i → PartialList A (L-reix kp i))
                (kss-suc (inj-l-+ (ms fzero) (sum m' ms') kp))
                (kss fzero kp)
      L-vs-bridge kp = kss-bridge-L m' ms mss kss kp

      R-vs-bridge :
        (kp : Fin (sum m' ms'))
        → PathP (λ i → PartialList A (R-reix kp i))
                (kss-suc (inj-r-+ (ms fzero) (sum m' ms') kp))
                (kss' _ _)
      R-vs-bridge kp = kss-bridge-R m' ms mss kss kp

      inner-from-push :
        PartialList A (sum (ms fzero) (C-suc ∘ inj-l-+ (ms fzero) (sum m' ms')))
      inner-from-push = pl-comp A (ms fzero)
                                 (C-suc ∘ inj-l-+ (ms fzero) (sum m' ms'))
                                 (ks fzero)
                                 (kss-suc ∘ inj-l-+ (ms fzero) (sum m' ms'))

      outer-from-push :
        PartialList A (sum (sum m' ms')
                            (C-suc ∘ inj-r-+ (ms fzero) (sum m' ms')))
      outer-from-push = pl-comp A (sum m' ms')
                                 (C-suc ∘ inj-r-+ (ms fzero) (sum m' ms'))
                                 (pl-comp A m' ms' ys ks')
                                 (kss-suc ∘ inj-r-+ (ms fzero) (sum m' ms'))

      L-bridge :
        PathP (λ i → PartialList A (sum (ms fzero) (λ kp → L-reix kp i)))
              inner-from-push inner
      L-bridge i = pl-comp A (ms fzero) (λ kp → L-reix kp i) (ks fzero)
                            (λ kp → L-vs-bridge kp i)

      R-bridge :
        PathP (λ i → PartialList A (sum (sum m' ms') (λ kp → R-reix kp i)))
              outer-from-push outer-RHS-rec
      R-bridge i = pl-comp A (sum m' ms') (λ kp → R-reix kp i)
                            (pl-comp A m' ms' ys ks')
                            (λ kp → R-vs-bridge kp i)

      stage-β :
        PathP (λ i → PartialList A
                       (sum (ms fzero) (λ kp → L-reix kp i)
                        + sum (sum m' ms') (λ kp → R-reix kp i)))
              (inner-from-push ++ outer-from-push)
              (inner ++ outer-RHS-rec)
      stage-β i = L-bridge i ++ R-bridge i

      push :
        PathP (λ i → PartialList A (sum-split (ms fzero) (sum m' ms') C-suc i))
              (pl-comp A (sum (suc m') ms) C-suc
                       (ks fzero ++ pl-comp A m' ms' ys ks') kss-suc)
              (inner-from-push ++ outer-from-push)
      push = pl-comp-++ (ms fzero) (sum m' ms') (ks fzero)
                        (pl-comp A m' ms' ys ks') C-suc kss-suc

      composite :
        PathP (λ i → PartialList A
                       (((λ i₁ →
                            sum (ms fzero) (mss fzero)
                            + Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 m' ms' mss') i₁)
                          ∙ sym (λ i₁ →
                                   sum (ms fzero) (λ kp → L-reix kp i₁)
                                   + sum (sum m' ms') (λ kp → R-reix kp i₁))
                          ∙ sym (sum-split (ms fzero) (sum m' ms') C-suc)) i))
              (inner ++ outer-LHS-rec)
              (pl-comp A (sum (suc m') ms) C-suc
                       (ks fzero ++ pl-comp A m' ms' ys ks') kss-suc)
      composite = compPathP' {B = PartialList A} stage-α
                  (compPathP' {B = PartialList A} (symP stage-β) (symP push))

opaque
  pl-assoc : (A : Type ℓ) (m : ℕ) (ms : Fin m → ℕ)
             (mss : (a : Fin m) → Fin (ms a) → ℕ)
             (k : PartialList A m) (ks : (a : Fin m) → PartialList A (ms a))
             (kss : (a : Fin m) (b : Fin (ms a)) → PartialList A (mss a b))
           → PathP (λ i → PartialList A (Universe.Inj 𝓝 (Universe.⅀Assoc≃ 𝓝 m ms mss) i))
                   (pl-comp A m (λ a → sum (ms a) (mss a)) k
                            (λ a → pl-comp A (ms a) (mss a) (ks a) (kss a)))
                   (pl-comp A (sum m ms) (Universe.⅀Assoc-C' 𝓝 m ms mss)
                            (pl-comp A m ms k ks)
                            (λ ab → kss _ _))
  pl-assoc A m ms mss k ks kss = pl-assoc-aux m ms mss k ks kss

------------------------------------------------------------------------
-- The PartialList operad.
------------------------------------------------------------------------
PartialListOperad : (A : Type ℓ) → isSet A → NonSymmOperad (PartialList A)
Operad.isSetK (PartialListOperad A isSetA) = isSetPartialList isSetA
Operad.id     (PartialListOperad A isSetA) = poke []
Operad.compₒ  (PartialListOperad A isSetA) = pl-comp A
Operad.idl    (PartialListOperad A isSetA) = pl-idl A
Operad.idr    (PartialListOperad A isSetA) = pl-idr A
Operad.assoc  (PartialListOperad A isSetA) = pl-assoc A
