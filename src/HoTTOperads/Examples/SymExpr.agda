{-# OPTIONS --cubical #-}
module HoTTOperads.Examples.SymExpr where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_ ; invEq ; equivEq ; invEquiv ; compEquiv
                                              ; idEquiv ; secEq ; retEq)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaInvEquiv ; uaCompEquiv ; uaIdEquiv ; EquivJ
                                                   ; pathToEquiv ; ua-pathToEquiv ; uaβ)
open import Cubical.Data.Sigma.Properties using (Σ-assoc-≃ ; Σ-cong-equiv-fst ; Σ-cong-equiv-snd)
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Functions.FunExtEquiv using (funExtDep)
open import Cubical.Data.FinSet.Base using (FinSet ; isGroupoidFinSet ; isPropIsFinSet)
open import Cubical.Data.FinSet.Properties using (isFinSet⊥)
open import Cubical.Data.FinSet.Constructors using (isFinSet⊎)
open import Cubical.Data.Nat using (ℕ ; suc ; isSetℕ)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Empty using (⊥) renaming (rec to ⊥-rec)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Universe.Instances.FinSet using (𝓕)
open import HoTTOperads.Prelude.FinSet using (un ; un-sym ; cong-fst-Σ≡Prop ; Σ≡Prop-∙ ; Σ≡Prop-inj)
open import Cubical.Data.Sum.Properties using (⊎-equiv)
open import HoTTOperads.Operad.Base
open import HoTTOperads.Operad.Specialised.Symm using (SymmOperad)

private
  variable
    ℓ : Level

open UniverseHelpers 𝓕

------------------------------------------------------------------------
-- Empty FinSet and binary FinSet coproduct, packaged locally.
------------------------------------------------------------------------
∅̂ : FinSet ℓ-zero
∅̂ = ⊥ , isFinSet⊥

_⊎̂_ : FinSet ℓ-zero → FinSet ℓ-zero → FinSet ℓ-zero
A ⊎̂ B = (El A ⊎ El B) , isFinSet⊎ A B

infixr 5 _⊎̂_

------------------------------------------------------------------------
-- Three FinSet-level paths used by sym-comp: singleton, empty, and
-- distributivity. Each lifts an underlying type-level equivalence via
-- `un` (the FinSet-univalence from HoTTOperads.Prelude.FinSet).
------------------------------------------------------------------------

-- The "empty Σ" equivalence, lifted from inside ∅̂-Σ-path's where-clause so
-- that downstream proofs (sym-idr at val↑) can refer to it.  Kept transparent:
-- its .equiv-proof is consumed by `invEquiv` and `un-sym` later.
empty-Σ-≃ : {X : ⊥ → Type ℓ-zero} → ⊥ ≃ Σ ⊥ X
empty-Σ-≃ = isoToEquiv (iso (λ x → ⊥-rec x)
                            (λ p → ⊥-rec (fst p))
                            (λ p → ⊥-rec (fst p))
                            (λ x → ⊥-rec x))

-- The distributivity iso between (Σ A₁ B ∘ inl) ⊎ (Σ A₂ B ∘ inr) and Σ (A₁ ⊎ A₂) B,
-- lifted out of ⊎̂-distr-path so sym-idr's add↑ case can refer to it.
distr-iso : (A₁ A₂ : FinSet ℓ-zero) (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
          → Iso ((Σ (El A₁) (λ a → El (B (inl a))))
                 ⊎ (Σ (El A₂) (λ a → El (B (inr a)))))
                (Σ (El A₁ ⊎ El A₂) (λ x → El (B x)))
Iso.fun (distr-iso _ _ _) (inl (a , b)) = inl a , b
Iso.fun (distr-iso _ _ _) (inr (a , b)) = inr a , b
Iso.inv (distr-iso _ _ _) (inl a , b) = inl (a , b)
Iso.inv (distr-iso _ _ _) (inr a , b) = inr (a , b)
Iso.rightInv (distr-iso _ _ _) (inl _ , _) = refl
Iso.rightInv (distr-iso _ _ _) (inr _ , _) = refl
Iso.leftInv (distr-iso _ _ _) (inl (_ , _)) = refl
Iso.leftInv (distr-iso _ _ _) (inr (_ , _)) = refl

opaque
  𝜏-Σ-path : (B : El 𝜏 → FinSet ℓ-zero) → B tt ≡ ⅀ 𝜏 B
  𝜏-Σ-path B = un (B tt) (⅀ 𝜏 B) Σ-idl-≃

  ∅̂-Σ-path : (B : El ∅̂ → FinSet ℓ-zero) → ∅̂ ≡ ⅀ ∅̂ B
  ∅̂-Σ-path B = un ∅̂ (⅀ ∅̂ B) empty-Σ-≃

  ⊎̂-distr-path : (A₁ A₂ : FinSet ℓ-zero) (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
               → ⅀ A₁ (B ∘ inl) ⊎̂ ⅀ A₂ (B ∘ inr) ≡ ⅀ (A₁ ⊎̂ A₂) B
  ⊎̂-distr-path A₁ A₂ B = un _ _ (isoToEquiv (distr-iso A₁ A₂ B))

------------------------------------------------------------------------
-- A symmetric analogue of IExpr, indexed by FinSet rather than ℕ.
-- val↑ at the empty FinSet matches the paper's convention (and the
-- IExpr.val↑ : IExpr 0 analogy); add↑ is the new binary constructor.
------------------------------------------------------------------------
data SymExpr : FinSet ℓ-zero → Type₁ where
  id↑  : SymExpr 𝜏
  val↑ : ℕ → SymExpr ∅̂
  add↑ : ∀ {A B} → SymExpr A → SymExpr B → SymExpr (A ⊎̂ B)

------------------------------------------------------------------------
-- Unindexed underlying tree, used as the target of a retract to prove
-- isSet (SymExpr A). Tree is a free inductive type, so isSet Tree is
-- the standard encode-decode argument.
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
-- Shape and forgetful map between Tree and SymExpr.
------------------------------------------------------------------------
shape : Tree → FinSet ℓ-zero
shape Tid          = 𝜏
shape (Tval _)     = ∅̂
shape (Tadd t₁ t₂) = shape t₁ ⊎̂ shape t₂

forget : ∀ {A} → SymExpr A → Tree
forget id↑          = Tid
forget (val↑ n)     = Tval n
forget (add↑ e₁ e₂) = Tadd (forget e₁) (forget e₂)

shape-correct : ∀ {A} (e : SymExpr A) → shape (forget e) ≡ A
shape-correct id↑          = refl
shape-correct (val↑ _)     = refl
shape-correct (add↑ e₁ e₂) = cong₂ _⊎̂_ (shape-correct e₁) (shape-correct e₂)

canonical : (t : Tree) → SymExpr (shape t)
canonical Tid          = id↑
canonical (Tval n)     = val↑ n
canonical (Tadd t₁ t₂) = add↑ (canonical t₁) (canonical t₂)

------------------------------------------------------------------------
-- Pushing subst through add↑, mirroring IExpr's subst-add↑.
------------------------------------------------------------------------
opaque
  subst-add↑ : {A₁ A₁' A₂ A₂' : FinSet ℓ-zero}
               (p₁ : A₁ ≡ A₁') (p₂ : A₂ ≡ A₂')
               (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
             → subst SymExpr (cong₂ _⊎̂_ p₁ p₂) (add↑ e₁ e₂)
             ≡ add↑ (subst SymExpr p₁ e₁) (subst SymExpr p₂ e₂)
  subst-add↑ p₁ p₂ e₁ e₂ =
    fromPathP (λ i → add↑ (subst-filler SymExpr p₁ e₁ i)
                          (subst-filler SymExpr p₂ e₂ i))

------------------------------------------------------------------------
-- The retract pair (f, g) and the round-trip g ∘ f ≡ id.
------------------------------------------------------------------------
SymTreeΣ : FinSet ℓ-zero → Type₁
SymTreeΣ A = Σ[ t ∈ Tree ] (shape t ≡ A)

f : ∀ {A} → SymExpr A → SymTreeΣ A
f e = forget e , shape-correct e

g : ∀ {A} → SymTreeΣ A → SymExpr A
g (t , p) = subst SymExpr p (canonical t)

g∘f : ∀ {A} (e : SymExpr A) → g (f e) ≡ e
g∘f id↑          = substRefl {B = SymExpr} id↑
g∘f (val↑ n)     = substRefl {B = SymExpr} (val↑ n)
g∘f (add↑ e₁ e₂) =
    subst-add↑ (shape-correct e₁) (shape-correct e₂)
               (canonical (forget e₁)) (canonical (forget e₂))
  ∙ λ i → add↑ (g∘f e₁ i) (g∘f e₂ i)

------------------------------------------------------------------------
-- isSetSymExpr, by retract to SymTreeΣ.  SymTreeΣ A is a Σ of a set
-- (Tree) and a set (paths in the groupoid FinSet), so a set itself.
------------------------------------------------------------------------
opaque
  isSetSymTreeΣ : (A : FinSet ℓ-zero) → isSet (SymTreeΣ A)
  isSetSymTreeΣ A = isSetΣ isSetTree (λ t → isGroupoidFinSet (shape t) A)

  isSetSymExpr : (A : FinSet ℓ-zero) → isSet (SymExpr A)
  isSetSymExpr A = isOfHLevelRetract 2 f g g∘f (isSetSymTreeΣ A)

------------------------------------------------------------------------
-- The operadic composition, defined by induction on the SymExpr argument
-- (paper: SymmetricOperads.tex, lines 254-289).
--
--   id↑   : recurse-on-input via the singleton path B(tt) ≡ ⅀ 𝜏 B.
--   val↑  : transport val↑ along ∅̂ ≡ ⅀ ∅̂ B.
--   add↑  : split the family B by inl/inr, recurse, and transport along
--           the distributivity path ⅀ A₁ B₁ ⊎̂ ⅀ A₂ B₂ ≡ ⅀ (A₁ ⊎̂ A₂) B.
------------------------------------------------------------------------
sym-comp : (A : FinSet ℓ-zero) (B : El A → FinSet ℓ-zero)
         → SymExpr A → ((a : El A) → SymExpr (B a))
         → SymExpr (⅀ A B)
sym-comp _ B id↑ es =
  subst SymExpr (𝜏-Σ-path B) (es tt)
sym-comp _ B (val↑ n) es =
  subst SymExpr (∅̂-Σ-path B) (val↑ n)
sym-comp _ B (add↑ {A₁} {A₂} e₁ e₂) es =
  subst SymExpr (⊎̂-distr-path A₁ A₂ B)
    (add↑ (sym-comp A₁ (B ∘ inl) e₁ (es ∘ inl))
          (sym-comp A₂ (B ∘ inr) e₂ (es ∘ inr)))

------------------------------------------------------------------------
-- Generic PathP-cong for sym-comp.  Used as the SymExpr analogue of
-- IExpr-comp-PathP throughout the sym-assoc proof: every place we need
-- to bridge sym-comp heterogeneously over a FinSet path goes through
-- this lemma.  Sealed `opaque` so its body doesn't re-expand sym-comp
-- at every consumer.
------------------------------------------------------------------------
private
  opaque
    sym-comp-PathP :
      {A A' : FinSet ℓ-zero} (p : A ≡ A')
      {B : El A → FinSet ℓ-zero} {B' : El A' → FinSet ℓ-zero}
      (B-path : PathP (λ i → El (p i) → FinSet ℓ-zero) B B')
      {e : SymExpr A} {e' : SymExpr A'}
      (e-path : PathP (λ i → SymExpr (p i)) e e')
      {es : (a : El A) → SymExpr (B a)}
      {es' : (a' : El A') → SymExpr (B' a')}
      (es-path : PathP (λ i → (a : El (p i)) → SymExpr (B-path i a)) es es')
      → PathP (λ i → SymExpr (⅀ (p i) (B-path i)))
              (sym-comp _ B e es) (sym-comp _ B' e' es')
    sym-comp-PathP _ B-path e-path es-path i =
      sym-comp _ (B-path i) (e-path i) (es-path i)

------------------------------------------------------------------------
-- Helper: un (opaque) equals Inj (transparent on 𝓕) — both reduce to
-- Σ≡Prop (λ _ → isPropIsFinSet) (ua e).
------------------------------------------------------------------------
opaque
  unfolding un
  un≡Inj : (X Y : FinSet ℓ-zero) (e : El X ≃ El Y)
         → un X Y e ≡ Inj e
  un≡Inj _ _ _ = refl

------------------------------------------------------------------------
-- Equivalence-equality witnesses: identify the universe-level equivalences
-- ⅀Idl≃ / ⅀Idr≃ with the simpler ones used to build 𝜏-Σ-path / ∅̂-Σ-path.
-- Each compares two equivalences whose underlying functions agree pointwise.
------------------------------------------------------------------------
opaque
  ⅀Idl≃≡invΣidl : (A : FinSet ℓ-zero)
                → ⅀Idl≃ A ≡ invEquiv (Σ-idl-≃ {A = λ _ → El A})
  ⅀Idl≃≡invΣidl A = equivEq (funExt λ { (_ , a) → refl })

  ⅀Idr≃-𝜏≡invΣidl : ⅀Idr≃ 𝜏 ≡ invEquiv (Σ-idl-≃ {A = λ _ → El 𝜏})
  ⅀Idr≃-𝜏≡invΣidl = equivEq (funExt λ { (_ , _) → refl })

  ⅀Idr≃-∅̂≡invEmpty : ⅀Idr≃ ∅̂ ≡ invEquiv (empty-Σ-≃ {X = λ _ → El 𝜏})
  ⅀Idr≃-∅̂≡invEmpty = equivEq (funExt λ p → ⊥-rec (fst p))

------------------------------------------------------------------------
-- Path-equality lemmas.  Each identifies the FinSet path produced by the
-- subst-filler approach (sym of one of 𝜏-Σ-path / ∅̂-Σ-path) with the
-- FinSet path Inj (⅀Idl≃ A) / Inj (⅀Idr≃ A) that the operad law expects.
------------------------------------------------------------------------
opaque
  unfolding 𝜏-Σ-path ∅̂-Σ-path

  sym-idl-path : (A : FinSet ℓ-zero)
               → sym (𝜏-Σ-path (λ _ → A)) ≡ Inj (⅀Idl≃ A)
  sym-idl-path A =
      un-sym A (⅀ 𝜏 (λ _ → A)) Σ-idl-≃
    ∙ cong (un (⅀ 𝜏 (λ _ → A)) A) (sym (⅀Idl≃≡invΣidl A))
    ∙ un≡Inj (⅀ 𝜏 (λ _ → A)) A (⅀Idl≃ A)

  sym-idr-id↑-path : sym (𝜏-Σ-path (λ _ → 𝜏)) ≡ Inj (⅀Idr≃ 𝜏)
  sym-idr-id↑-path =
      un-sym 𝜏 (⅀ 𝜏 (λ _ → 𝜏)) Σ-idl-≃
    ∙ cong (un (⅀ 𝜏 (λ _ → 𝜏)) 𝜏) (sym ⅀Idr≃-𝜏≡invΣidl)
    ∙ un≡Inj (⅀ 𝜏 (λ _ → 𝜏)) 𝜏 (⅀Idr≃ 𝜏)

  sym-idr-val↑-path : sym (∅̂-Σ-path (λ _ → 𝜏)) ≡ Inj (⅀Idr≃ ∅̂)
  sym-idr-val↑-path =
      un-sym ∅̂ (⅀ ∅̂ (λ _ → 𝜏)) (empty-Σ-≃ {X = λ _ → El 𝜏})
    ∙ cong (un (⅀ ∅̂ (λ _ → 𝜏)) ∅̂) (sym ⅀Idr≃-∅̂≡invEmpty)
    ∙ un≡Inj (⅀ ∅̂ (λ _ → 𝜏)) ∅̂ (⅀Idr≃ ∅̂)

------------------------------------------------------------------------
-- Lifting cong₂ _⊎_ over ua-paths to a single ua-path on the ⊎-equiv.
-- Standard EquivJ reduction to the case where both equivalences are id.
------------------------------------------------------------------------
opaque
  ua-⊎ : {A A' B B' : Type ℓ-zero}
         (e₁ : A ≃ A') (e₂ : B ≃ B')
       → cong₂ _⊎_ (ua e₁) (ua e₂) ≡ ua (⊎-equiv e₁ e₂)
  ua-⊎ {A' = A'} {B' = B'} =
    EquivJ (λ _ e₁ → (e₂ : _ ≃ B')
                   → cong₂ _⊎_ (ua e₁) (ua e₂) ≡ ua (⊎-equiv e₁ e₂))
           (EquivJ (λ _ e₂ → cong₂ _⊎_ (ua (idEquiv A')) (ua e₂)
                           ≡ ua (⊎-equiv (idEquiv A') e₂))
                   base-case)
    where
      ⊎-id-≡-id : ⊎-equiv (idEquiv A') (idEquiv B') ≡ idEquiv (A' ⊎ B')
      ⊎-id-≡-id = equivEq (funExt λ { (inl _) → refl ; (inr _) → refl })

      base-case : cong₂ _⊎_ (ua (idEquiv A')) (ua (idEquiv B'))
                ≡ ua (⊎-equiv (idEquiv A') (idEquiv B'))
      base-case =
          (λ i → cong₂ _⊎_ (uaIdEquiv {A = A'} i) (uaIdEquiv {A = B'} i))
        ∙ sym uaIdEquiv
        ∙ cong ua (sym ⊎-id-≡-id)

------------------------------------------------------------------------
-- The add↑ path-equality.  Combines the sym of the distributivity path with
-- the ⊎̂-action of the IH-induced index paths, identifying the composite
-- with Inj (⅀Idr≃ (A₁ ⊎̂ A₂)).
------------------------------------------------------------------------
opaque
  -- `unfolding un` is required because the chain below bridges
  -- `cong fst (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏))` (which unfolds via
  -- `⊎̂-distr-path` to `cong fst (un … distr)`) with `ua distr` via
  -- `cong-fst-Σ≡Prop _ (ua distr)`. That bridge needs `un` to reduce
  -- to `Σ≡Prop _ (ua _)`. (Previously this worked through implicit
  -- normalisation when isFinSetΣ was transparent; with `isFinSetΣ-op`
  -- opaque the unifier no longer finds it on its own.)
  unfolding ⊎̂-distr-path un

  sym-idr-add↑-path : (A₁ A₂ : FinSet ℓ-zero)
                    → sym (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏))
                      ∙ cong₂ _⊎̂_ (Inj {A = ⅀ A₁ (λ _ → 𝜏)} {B = A₁} (⅀Idr≃ A₁))
                                   (Inj {A = ⅀ A₂ (λ _ → 𝜏)} {B = A₂} (⅀Idr≃ A₂))
                    ≡ Inj {A = ⅀ (A₁ ⊎̂ A₂) (λ _ → 𝜏)} {B = A₁ ⊎̂ A₂}
                          (⅀Idr≃ (A₁ ⊎̂ A₂))
  sym-idr-add↑-path A₁ A₂ =
    Σ≡Prop-inj (λ _ → isPropIsFinSet) _ _ fst-eq
    where
      distr : (Σ (El A₁) (λ _ → El 𝜏)) ⊎ (Σ (El A₂) (λ _ → El 𝜏))
            ≃ Σ (El A₁ ⊎ El A₂) (λ _ → El 𝜏)
      distr = isoToEquiv (distr-iso A₁ A₂ (λ _ → 𝜏))

      composite : (Σ (El A₁ ⊎ El A₂) (λ _ → El 𝜏)) ≃ (El A₁ ⊎ El A₂)
      composite = compEquiv (invEquiv distr)
                            (⊎-equiv (⅀Idr≃ A₁) (⅀Idr≃ A₂))

      composite≡⅀Idr : composite ≡ ⅀Idr≃ (A₁ ⊎̂ A₂)
      composite≡⅀Idr = equivEq (funExt λ { (inl _ , _) → refl
                                          ; (inr _ , _) → refl })

      -- Under opaque `isFinSetΣ-op`, Agda cannot infer Inj's `{A B : FinSet}`
      -- implicit args from `El A ≃ El B` alone (multiple FinSets share an
      -- underlying type), so they are spelled out at each call below.
      Inj-Idr₁ : ⅀ A₁ (λ _ → 𝜏) ≡ A₁
      Inj-Idr₁ = Inj {A = ⅀ A₁ (λ _ → 𝜏)} {B = A₁} (⅀Idr≃ A₁)

      Inj-Idr₂ : ⅀ A₂ (λ _ → 𝜏) ≡ A₂
      Inj-Idr₂ = Inj {A = ⅀ A₂ (λ _ → 𝜏)} {B = A₂} (⅀Idr≃ A₂)

      Inj-Idr-sum : ⅀ (A₁ ⊎̂ A₂) (λ _ → 𝜏) ≡ (A₁ ⊎̂ A₂)
      Inj-Idr-sum = Inj {A = ⅀ (A₁ ⊎̂ A₂) (λ _ → 𝜏)} {B = A₁ ⊎̂ A₂}
                        (⅀Idr≃ (A₁ ⊎̂ A₂))

      fst-LHS-step₁ : cong fst (sym (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏))
                                ∙ cong₂ _⊎̂_ Inj-Idr₁ Inj-Idr₂)
                    ≡ sym (cong fst (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏)))
                      ∙ cong₂ _⊎_ (cong fst Inj-Idr₁)
                                  (cong fst Inj-Idr₂)
      fst-LHS-step₁ =
        cong-∙ fst (sym (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏)))
                    (cong₂ _⊎̂_ Inj-Idr₁ Inj-Idr₂)

      fst-eq : cong fst (sym (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏))
                         ∙ cong₂ _⊎̂_ Inj-Idr₁ Inj-Idr₂)
             ≡ cong fst Inj-Idr-sum
      fst-eq =
          fst-LHS-step₁
        ∙ cong₂ _∙_
            (cong sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                         {u = ⅀ A₁ (λ _ → 𝜏) ⊎̂ ⅀ A₂ (λ _ → 𝜏)}
                         {v = ⅀ (A₁ ⊎̂ A₂) (λ _ → 𝜏)}
                         (ua distr)))
            -- Inlined as a path-of-paths. With isFinSetΣ-op opaque, the
            -- surrounding FinSet types no longer reduce, and Agda fails to
            -- solve the higher-order meta needed to apply
            -- `cong₂ (cong₂ _⊎_)` here. The explicit `λ i → ...` form
            -- side-steps the meta entirely.
            (λ i → cong₂ _⊎_ (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                                  {u = ⅀ A₁ (λ _ → 𝜏)} {v = A₁}
                                  (ua (⅀Idr≃ A₁)) i)
                              (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                                  {u = ⅀ A₂ (λ _ → 𝜏)} {v = A₂}
                                  (ua (⅀Idr≃ A₂)) i))
        ∙ cong (λ p → sym (ua distr) ∙ p) (ua-⊎ (⅀Idr≃ A₁) (⅀Idr≃ A₂))
        ∙ cong (_∙ ua (⊎-equiv (⅀Idr≃ A₁) (⅀Idr≃ A₂))) (sym (uaInvEquiv distr))
        ∙ sym (uaCompEquiv (invEquiv distr) (⊎-equiv (⅀Idr≃ A₁) (⅀Idr≃ A₂)))
        ∙ cong ua composite≡⅀Idr
        ∙ sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                  {u = ⅀ (A₁ ⊎̂ A₂) (λ _ → 𝜏)} {v = A₁ ⊎̂ A₂}
                  (ua (⅀Idr≃ (A₁ ⊎̂ A₂))))

------------------------------------------------------------------------
-- sym-idl: the operadic left-identity law.  The proof mirrors the IExpr
-- pattern (IExpr.agda:165-173) but uses sym-idl-path in place of isSetℕ.
------------------------------------------------------------------------
opaque
  sym-idl : (A : FinSet ℓ-zero) (k : SymExpr A)
          → PathP (λ i → SymExpr (Inj {A = ⅀ 𝜏 (λ _ → A)} {B = A} (⅀Idl≃ A) i))
                  (sym-comp 𝜏 (λ _ → A) id↑ (λ _ → k)) k
  sym-idl A k =
    subst (λ p → PathP (λ i → SymExpr (p i))
                       (sym-comp 𝜏 (λ _ → A) id↑ (λ _ → k)) k)
          (sym-idl-path A)
          (symP (subst-filler SymExpr (𝜏-Σ-path (λ _ → A)) k))

------------------------------------------------------------------------
-- sym-idr: the operadic right-identity law.  Inductive on k, mirroring the
-- IExpr-idr structure (IExpr.agda:180-213).  Each case packages a
-- subst-filler with the matching sym-idr-*-path swap.
------------------------------------------------------------------------
opaque
  sym-idr : (A : FinSet ℓ-zero) (k : SymExpr A)
          → PathP (λ i → SymExpr (Inj {A = ⅀ A (λ _ → 𝜏)} {B = A} (⅀Idr≃ A) i))
                  (sym-comp A (λ _ → 𝜏) k (λ _ → id↑)) k
  -- The dot-patterns `.𝜏`, `.∅̂`, `.(_ ⊎̂ _)` worked when ⅀FS was transparent
  -- but fail under opaque isFinSetΣ-op: Agda's parser interprets `.𝜏` as a
  -- copattern projection because `𝜏` is in scope as a record-field name from
  -- `open UniverseHelpers 𝓕`. Bare variable patterns let Agda recover the
  -- index of the SymExpr constructor (`id↑ : SymExpr 𝜏`, `val↑ _ : SymExpr ∅̂`,
  -- `add↑ … : SymExpr (_ ⊎̂ _)`) without going through the ambiguous syntax.
  sym-idr _ id↑ =
    subst (λ p → PathP (λ i → SymExpr (p i))
                       (sym-comp 𝜏 (λ _ → 𝜏) id↑ (λ _ → id↑)) id↑)
          sym-idr-id↑-path
          (symP (subst-filler SymExpr (𝜏-Σ-path (λ _ → 𝜏)) id↑))
  sym-idr _ (val↑ n) =
    subst (λ p → PathP (λ i → SymExpr (p i))
                       (sym-comp ∅̂ (λ _ → 𝜏) (val↑ n) (λ _ → id↑)) (val↑ n))
          sym-idr-val↑-path
          (symP (subst-filler SymExpr (∅̂-Σ-path (λ _ → 𝜏)) (val↑ n)))
  sym-idr _ (add↑ {A₁} {A₂} e₁ e₂) =
    subst (λ p → PathP (λ i → SymExpr (p i))
                       (sym-comp (A₁ ⊎̂ A₂) (λ _ → 𝜏) (add↑ e₁ e₂) (λ _ → id↑))
                       (add↑ e₁ e₂))
          (sym-idr-add↑-path A₁ A₂)
          (compPathP' {B = SymExpr} filler-path add↑-path)
    where
      recL : SymExpr (⅀ A₁ (λ _ → 𝜏))
      recL = sym-comp A₁ (λ _ → 𝜏) e₁ (λ _ → id↑)
      recR : SymExpr (⅀ A₂ (λ _ → 𝜏))
      recR = sym-comp A₂ (λ _ → 𝜏) e₂ (λ _ → id↑)
      filler-path : PathP (λ i → SymExpr (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏) (~ i)))
                          (sym-comp (A₁ ⊎̂ A₂) (λ _ → 𝜏) (add↑ e₁ e₂) (λ _ → id↑))
                          (add↑ recL recR)
      filler-path = symP (subst-filler SymExpr (⊎̂-distr-path A₁ A₂ (λ _ → 𝜏))
                                                (add↑ recL recR))
      add↑-path : PathP (λ i → SymExpr (Inj {A = ⅀ A₁ (λ _ → 𝜏)} {B = A₁}
                                              (⅀Idr≃ A₁) i
                                          ⊎̂ Inj {A = ⅀ A₂ (λ _ → 𝜏)} {B = A₂}
                                                  (⅀Idr≃ A₂) i))
                         (add↑ recL recR) (add↑ e₁ e₂)
      add↑-path i = add↑ (sym-idr A₁ e₁ i) (sym-idr A₂ e₂ i)

------------------------------------------------------------------------
-- §A  Associativity, val↑ case.
--
-- For IExpr the val↑ case was `refl` because `0 + x ≡ x` definitionally.
-- For SymExpr `⅀ ∅̂ B` is *not* `∅̂` definitionally, so the outer sym-comp
-- on the RHS cannot pattern-match into the transported val↑.
--
-- Strategy: lift the outer sym-comp back to the ∅̂ side via sym-comp-PathP
-- with vacuous family/es PathPs (both built by `funExtDep ⊥-rec`). The
-- resulting bridge has the LHS and RHS of sym-assoc as endpoints, indexed
-- over a structural FinSet path. The path-equality swap is handled by
-- `empty-FinSet-paths-isProp`: paths in FinSet between two FinSets one
-- of which is empty form a proposition (because the equivalence type
-- between empty types is contractible).
------------------------------------------------------------------------

private
  opaque
    -- The vacuous family-PathP: both endpoints reduce on `El ∅̂ = ⊥`.
    B-path-val↑ : (B : El ∅̂ → FinSet ℓ-zero)
                  (C : (a : El ∅̂) → El (B a) → FinSet ℓ-zero)
                → PathP (λ i → El (∅̂-Σ-path B i) → FinSet ℓ-zero)
                        (λ a → ⅀ (B a) (C a))
                        (⅀Assoc-C' ∅̂ B C)
    B-path-val↑ _ _ = funExtDep λ {a₀} _ → ⊥-rec a₀

    -- The vacuous dependent-function PathP for the kss-application.
    es-path-val↑ : (B : El ∅̂ → FinSet ℓ-zero)
                   (C : (a : El ∅̂) → El (B a) → FinSet ℓ-zero)
                   (ks : (a : El ∅̂) → SymExpr (B a))
                   (kss : (a : El ∅̂) (b : El (B a)) → SymExpr (C a b))
                 → PathP (λ i → (a : El (∅̂-Σ-path B i))
                              → SymExpr (B-path-val↑ B C i a))
                         (λ a → sym-comp (B a) (C a) (ks a) (kss a))
                         (λ ab → kss _ _)
    es-path-val↑ _ _ _ _ = funExtDep λ {a₀} _ → ⊥-rec a₀

opaque
  -- Paths in FinSet between two FinSets one of which is empty form a
  -- proposition.  Reason: by Σ≡Prop-inj, comparison reduces to the
  -- underlying Type-paths.  By univalence each Type-path corresponds
  -- to an equivalence; for empty domains all equivalences are equal
  -- (their function parts agree pointwise via ⊥-rec).
  empty-FinSet-paths-isProp :
    (X Y : FinSet ℓ-zero) (X-empty : El X → ⊥) → isProp (X ≡ Y)
  empty-FinSet-paths-isProp X Y X-empty p q =
    Σ≡Prop-inj (λ _ → isPropIsFinSet) p q fst-eq
    where
      fst-eq : cong fst p ≡ cong fst q
      fst-eq = sym (ua-pathToEquiv (cong fst p))
             ∙ cong ua (equivEq (funExt λ x → ⊥-rec (X-empty x)))
             ∙ ua-pathToEquiv (cong fst q)

opaque
  unfolding sym-comp-PathP B-path-val↑ es-path-val↑

  sym-assoc-val↑ :
    (n : ℕ) (B : El ∅̂ → FinSet ℓ-zero)
    (C : (a : El ∅̂) → El (B a) → FinSet ℓ-zero)
    (ks : (a : El ∅̂) → SymExpr (B a))
    (kss : (a : El ∅̂) (b : El (B a)) → SymExpr (C a b))
    → PathP (λ i → SymExpr (Inj {A = ⅀ ∅̂ (λ a → ⅀ (B a) (C a))}
                                   {B = ⅀ (⅀ ∅̂ B) (⅀Assoc-C' ∅̂ B C)}
                                   (⅀Assoc≃ ∅̂ B C) i))
            (sym-comp ∅̂ (λ a → ⅀ (B a) (C a)) (val↑ n)
                      (λ a → sym-comp (B a) (C a) (ks a) (kss a)))
            (sym-comp (⅀ ∅̂ B) (⅀Assoc-C' ∅̂ B C)
                      (sym-comp ∅̂ B (val↑ n) ks)
                      (λ ab → kss _ _))
  sym-assoc-val↑ n B C ks kss =
    subst (λ p → PathP (λ i → SymExpr (p i))
                       (sym-comp ∅̂ (λ a → ⅀ (B a) (C a)) (val↑ n)
                                 (λ a → sym-comp (B a) (C a) (ks a) (kss a)))
                       (sym-comp (⅀ ∅̂ B) (⅀Assoc-C' ∅̂ B C)
                                 (sym-comp ∅̂ B (val↑ n) ks)
                                 (λ ab → kss _ _)))
          (empty-FinSet-paths-isProp _ _ (λ p → fst p) _ _)
          bridge
    where
      bridge : PathP (λ i → SymExpr (⅀ (∅̂-Σ-path B i) (B-path-val↑ B C i)))
                     (sym-comp ∅̂ (λ a → ⅀ (B a) (C a)) (val↑ n)
                               (λ a → sym-comp (B a) (C a) (ks a) (kss a)))
                     (sym-comp (⅀ ∅̂ B) (⅀Assoc-C' ∅̂ B C)
                               (sym-comp ∅̂ B (val↑ n) ks)
                               (λ ab → kss _ _))
      bridge = sym-comp-PathP (∅̂-Σ-path B) (B-path-val↑ B C)
                              (subst-filler SymExpr (∅̂-Σ-path B) (val↑ n))
                              (es-path-val↑ B C ks kss)

------------------------------------------------------------------------
-- §B  Associativity, id↑ case.
--
-- Mirrors IExpr-assoc-id↑ (IExpr.agda §9): outer subst-filler reversal
-- composed with an `IExpr-comp-PathP` (here `sym-comp-PathP`) bridge.
-- The Cubical novelty for FinSet: we need to compute
-- `transport (cong El (𝜏-Σ-path B)) a ≡ (tt , a)` to extract a
-- homogeneous El-(B tt)-path from the heterogeneous PathP that funExtDep
-- hands us.  This is `transp-El-𝜏-Σ-path`.
------------------------------------------------------------------------

private
  opaque
    unfolding 𝜏-Σ-path un cong-fst-Σ≡Prop
    -- Computes the transport of `B tt`-elements along `𝜏-Σ-path B` to the
    -- explicit pair `(tt , a)`.  Sealed once and consumed by name later;
    -- callers never need to re-unfold `un` or `cong-fst-Σ≡Prop`.
    transp-El-𝜏-Σ-path : (B : El 𝜏 → FinSet ℓ-zero) (a : El (B tt))
                       → transport (λ i → El (𝜏-Σ-path B i)) a ≡ (tt , a)
    transp-El-𝜏-Σ-path B a =
        cong (λ p → transport p a)
             (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                              {u = B tt} {v = ⅀ 𝜏 B}
                              (ua (Σ-idl-≃ {A = El ∘ B})))
      ∙ uaβ (Σ-idl-≃ {A = El ∘ B}) a

  opaque
    -- The aligning family-PathP between `C tt` and `⅀Assoc-C' 𝜏 B C`.
    -- By Unit-η, `⅀Assoc-C' 𝜏 B C a = C tt (snd a)`, so the path
    -- reduces to `cong (C tt)` of an `a₀ ≡ snd a₁` extracted from
    -- a-path via `transp-El-𝜏-Σ-path` + `fromPathP`.
    B-path-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                 (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
               → PathP (λ i → El (𝜏-Σ-path B i) → FinSet ℓ-zero)
                       (C tt) (⅀Assoc-C' 𝜏 B C)
    B-path-id↑ B C = funExtDep λ {a₀} {a₁} a-path →
      cong (λ p → C (fst p) (snd p))
           (sym (transp-El-𝜏-Σ-path B a₀) ∙ fromPathP a-path)

  opaque
    unfolding B-path-id↑
    -- The kss-application twin of B-path-id↑.  Bridges `kss tt` (the
    -- inner kss-application at a = tt) and the RHS `λ ab → kss _ _`.
    es-path-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                  (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                  (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
                → PathP (λ i → (a : El (𝜏-Σ-path B i))
                              → SymExpr (B-path-id↑ B C i a))
                        (kss tt)
                        (λ ab → kss (fst ab) (snd ab))
    es-path-id↑ B C kss = funExtDep λ {a₀} {a₁} a-path →
      cong (λ p → kss (fst p) (snd p))
           (sym (transp-El-𝜏-Σ-path B a₀) ∙ fromPathP a-path)

postulate
  sym-assoc : (A : FinSet ℓ-zero) (B : El A → FinSet ℓ-zero)
              (C : (a : El A) → El (B a) → FinSet ℓ-zero)
              (k : SymExpr A) (ks : (a : El A) → SymExpr (B a))
              (kss : (a : El A) (b : El (B a)) → SymExpr (C a b))
            → PathP (λ i → SymExpr (Inj {A = ⅀ A (λ a → ⅀ (B a) (C a))}
                                         {B = ⅀ (⅀ A B) (⅀Assoc-C' A B C)}
                                         (⅀Assoc≃ A B C) i))
                    (sym-comp A (λ a → ⅀ (B a) (C a)) k
                              (λ a → sym-comp (B a) (C a) (ks a) (kss a)))
                    (sym-comp (⅀ A B) (⅀Assoc-C' A B C)
                              (sym-comp A B k ks)
                              (λ ab → kss _ _))

SymExprOperad : SymmOperad SymExpr
Operad.isSetK SymExprOperad = isSetSymExpr
Operad.id     SymExprOperad = id↑
Operad.compₒ  SymExprOperad = sym-comp
Operad.idl    SymExprOperad = sym-idl
Operad.idr    SymExprOperad = sym-idr
Operad.assoc  SymExprOperad = sym-assoc
