{-# OPTIONS --cubical #-}
module HoTTOperads.Examples.SymExpr where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv using (_≃_ ; invEq ; equivEq ; invEquiv ; compEquiv
                                              ; idEquiv ; secEq ; retEq ; equivFun)
open import Cubical.Foundations.Isomorphism using (Iso ; iso ; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua ; uaInvEquiv ; uaCompEquiv ; uaIdEquiv ; EquivJ
                                                   ; pathToEquiv ; ua-pathToEquiv ; uaβ ; ua-unglue
                                                   ; unglue)
open import Cubical.Data.Sigma.Properties using (Σ-assoc-≃ ; Σ-cong-equiv-fst ; Σ-cong-equiv-snd)
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Functions.FunExtEquiv using (funExtDep ; funExtDepEquiv)
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
-- `fun` and `leftInv` are written uniformly with `fst`/`snd` (relying
-- on Σ-η) instead of pattern matching on `(a , b)`.  This makes
-- `Iso.fun distr-iso (inl ab)` reduce on a generic `ab`, which the
-- add↑-case boundary checks rely on.
Iso.fun (distr-iso _ _ _) (inl ab) = inl (fst ab) , snd ab
Iso.fun (distr-iso _ _ _) (inr ab) = inr (fst ab) , snd ab
Iso.inv (distr-iso _ _ _) (inl a , b) = inl (a , b)
Iso.inv (distr-iso _ _ _) (inr a , b) = inr (a , b)
Iso.rightInv (distr-iso _ _ _) (inl _ , _) = refl
Iso.rightInv (distr-iso _ _ _) (inr _ , _) = refl
Iso.leftInv (distr-iso _ _ _) (inl _) = refl
Iso.leftInv (distr-iso _ _ _) (inr _) = refl

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
-- Σ-cong over an ua-path on the first factor, identified with ua of
-- Σ-cong-equiv-fst.  Like ua-⊎, by EquivJ reduction to the identity case.
-- The Σ-of-paths form `λ i → Σ (ua e i) (G ∘ ua-unglue e i)` is what
-- emerges from `cong fst` on FinSet paths built via the universe's `un`.
------------------------------------------------------------------------
opaque
  Σ-cong-equiv-fst-ua : {A A' : Type ℓ-zero} (e : A ≃ A') (G : A' → Type ℓ-zero)
                      → (λ i → Σ (ua e i) (λ x → G (ua-unglue e i x)))
                      ≡ ua (Σ-cong-equiv-fst {B = G} e)
  Σ-cong-equiv-fst-ua {A' = A'} e G =
    EquivJ (λ A e → (λ i → Σ (ua e i) (λ x → G (ua-unglue e i x)))
                  ≡ ua (Σ-cong-equiv-fst {B = G} e))
           base-case e
    where
      Σ-cong-id-≡-id : Σ-cong-equiv-fst {B = G} (idEquiv A') ≡ idEquiv (Σ A' G)
      Σ-cong-id-≡-id = equivEq (funExt λ { (_ , _) → refl })

      -- Smoother base-case path that varies the Glue domain in j synchronously
      -- with the unglue projection.  At j=0: the LHS of base-case (uaIdEquiv 0 i
      -- = ua (idEquiv A') i and unglue (~i ∨ i) = ua-unglue (idEquiv A') i).
      -- At j=1: Σ A' G (constant), since uaIdEquiv 1 i = A' and unglue i1 = id.
      base-case : (λ i → Σ (ua (idEquiv A') i) (λ x → G (ua-unglue (idEquiv A') i x)))
                ≡ ua (Σ-cong-equiv-fst {B = G} (idEquiv A'))
      base-case =
          (λ j i → Σ (uaIdEquiv {A = A'} j i)
                     (λ x → G (unglue (j ∨ ~ i ∨ i) x)))
        ∙ sym uaIdEquiv
        ∙ cong ua (sym Σ-cong-id-≡-id)

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
    unfolding 𝜏-Σ-path un
    -- B-path-id↑ via `ua-unglue`: with `𝜏-Σ-path B = Σ≡Prop pp (ua Σ-idl-≃)`,
    -- the underlying type-path `cong El (𝜏-Σ-path B)` reduces definitionally
    -- to `ua Σ-idl-≃` (because `cong fst (Σ≡Prop pp p) = p` is definitional
    -- in Cubical via the `ΣPathP`-style construction inside Σ≡Prop).  So
    -- `El (𝜏-Σ-path B i) = ua (Σ-idl-≃ {A = El ∘ B}) i` definitionally.
    -- We then use `ua-unglue Σ-idl-≃ i a` to bring `a` to `El (⅀ 𝜏 B)`,
    -- and apply `⅀Assoc-C' 𝜏 B C`.  At i=0 this is `C tt a` (Unit-η on
    -- `fst (tt, a)`); at i=1 this is `⅀Assoc-C' 𝜏 B C a`.  Both boundary
    -- reductions are *definitional*, so consumers (`es-path-id↑`,
    -- `bridge-id↑`, the path-equality lemma) typecheck cleanly without
    -- the funExtDep + Glue-elimination dance.
    B-path-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                 (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
               → PathP (λ i → El (𝜏-Σ-path B i) → FinSet ℓ-zero)
                       (C tt) (⅀Assoc-C' 𝜏 B C)
    B-path-id↑ B C i a =
      ⅀Assoc-C' 𝜏 B C (ua-unglue (Σ-idl-≃ {A = El ∘ B}) i a)

  opaque
    unfolding 𝜏-Σ-path un B-path-id↑
    -- es-path-id↑ via the same `ua-unglue` machinery.  The motive
    -- `SymExpr (B-path-id↑ B C i a)` reduces definitionally to
    -- `SymExpr (⅀Assoc-C' 𝜏 B C (ua-unglue Σ-idl-≃ i a))` =
    -- `SymExpr (C tt (snd (ua-unglue Σ-idl-≃ i a)))` (Unit-η).
    -- The body `kss tt (snd (ua-unglue …))` matches at both boundaries.
    es-path-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                  (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                  (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
                → PathP (λ i → (a : El (𝜏-Σ-path B i))
                              → SymExpr (B-path-id↑ B C i a))
                        (kss tt)
                        (λ ab → kss (fst ab) (snd ab))
    es-path-id↑ B C kss i a =
      kss tt (snd (ua-unglue (Σ-idl-≃ {A = El ∘ B}) i a))

  -- The three endpoints of the id↑-case PathP and their bridges.
  opaque
    Xinner-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                 (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                 (ks : (a : El 𝜏) → SymExpr (B a))
                 (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
               → SymExpr (⅀ (B tt) (C tt))
    Xinner-id↑ B C ks kss = sym-comp (B tt) (C tt) (ks tt) (kss tt)

  opaque
    unfolding Xinner-id↑
    lhs-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
              (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
              (ks : (a : El 𝜏) → SymExpr (B a))
              (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
            → SymExpr (⅀ 𝜏 (λ a → ⅀ (B a) (C a)))
    lhs-id↑ B C ks kss =
      subst SymExpr (𝜏-Σ-path (λ a → ⅀ (B a) (C a))) (Xinner-id↑ B C ks kss)

  opaque
    rhs-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
              (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
              (ks : (a : El 𝜏) → SymExpr (B a))
              (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
            → SymExpr (⅀ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C))
    rhs-id↑ B C ks kss =
      sym-comp (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)
               (subst SymExpr (𝜏-Σ-path B) (ks tt))
               (λ ab → kss (fst ab) (snd ab))

  opaque
    unfolding Xinner-id↑ rhs-id↑ sym-comp-PathP
    -- Recipe (b): sym-comp-PathP over 𝜏-Σ-path B with B-path-id↑ and es-path-id↑.
    bridge-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                 (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                 (ks : (a : El 𝜏) → SymExpr (B a))
                 (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
               → PathP (λ i → SymExpr (⅀ (𝜏-Σ-path B i) (B-path-id↑ B C i)))
                       (Xinner-id↑ B C ks kss)
                       (rhs-id↑ B C ks kss)
    bridge-id↑ B C ks kss =
      sym-comp-PathP (𝜏-Σ-path B) (B-path-id↑ B C)
                     (subst-filler SymExpr (𝜏-Σ-path B) (ks tt))
                     (es-path-id↑ B C kss)

  opaque
    unfolding Xinner-id↑ lhs-id↑
    -- Recipe (a): subst-filler reversal from lhs-id↑ to Xinner-id↑.
    outer-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                (ks : (a : El 𝜏) → SymExpr (B a))
                (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
              → PathP (λ i → SymExpr (𝜏-Σ-path (λ a → ⅀ (B a) (C a)) i))
                      (Xinner-id↑ B C ks kss) (lhs-id↑ B C ks kss)
    outer-id↑ B C ks kss =
      subst-filler SymExpr (𝜏-Σ-path (λ a → ⅀ (B a) (C a)))
                            (Xinner-id↑ B C ks kss)

  -- The composed structural FinSet path used by the id↑-case PathP.
  opaque
    chosen-path-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                      (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                    → ⅀ 𝜏 (λ a → ⅀ (B a) (C a))
                    ≡ ⅀ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)
    chosen-path-id↑ B C =
        sym (𝜏-Σ-path (λ a → ⅀ (B a) (C a)))
      ∙ (λ i → ⅀ (𝜏-Σ-path B i) (B-path-id↑ B C i))

  opaque
    unfolding chosen-path-id↑
    my-PathP-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                   (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                   (ks : (a : El 𝜏) → SymExpr (B a))
                   (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
                 → PathP (λ i → SymExpr (chosen-path-id↑ B C i))
                         (lhs-id↑ B C ks kss) (rhs-id↑ B C ks kss)
    my-PathP-id↑ B C ks kss =
      compPathP' {B = SymExpr} (symP (outer-id↑ B C ks kss))
                                (bridge-id↑ B C ks kss)

------------------------------------------------------------------------
-- Path-equality lemma for the id↑ case.  Structural composite
-- `chosen-path-id↑ = sym (𝜏-Σ-path …) ∙ Σ-of-paths-leg`.  We show its
-- cong-fst equals cong-fst of `Inj (⅀Assoc≃ 𝜏 B C)` by chaining
-- `cong-∙ fst`, the leg-1 `cong-fst-Σ≡Prop` reduction, and the leg-2
-- `Σ-cong-equiv-fst-ua` identification; merge with `uaInvEquiv` and
-- `uaCompEquiv` and identify the composite equiv with `⅀Assoc≃ 𝜏 B C`
-- via a pointwise `equivEq` on explicit compositions (no Glue).
------------------------------------------------------------------------

opaque
  unfolding chosen-path-id↑ B-path-id↑ 𝜏-Σ-path un

  sym-assoc-id↑-path : (B : El 𝜏 → FinSet ℓ-zero)
                       (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                     → chosen-path-id↑ B C
                     ≡ Inj {A = ⅀ 𝜏 (λ a → ⅀ (B a) (C a))}
                            {B = ⅀ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)}
                            (⅀Assoc≃ 𝜏 B C)
  sym-assoc-id↑-path B C =
    Σ≡Prop-inj (λ _ → isPropIsFinSet) _ _ fst-eq
    where
      -- Inner Σ-idl-≃ (the one that appears in 𝜏-Σ-path B) and outer
      -- Σ-idl-≃ (the one in 𝜏-Σ-path (λ a → ⅀ (B a) (C a))).
      Σ-idl-inner : El (B tt) ≃ Σ (El 𝜏) (El ∘ B)
      Σ-idl-inner = Σ-idl-≃ {A = El ∘ B}

      Σ-idl-outer : Σ (El (B tt)) (El ∘ C tt)
                  ≃ Σ (El 𝜏) (λ a → Σ (El (B a)) (El ∘ C a))
      Σ-idl-outer = Σ-idl-≃ {A = λ a → Σ (El (B a)) (El ∘ C a)}

      -- Explicit composite equivalence whose action matches ⅀Assoc≃ 𝜏 B C
      -- pointwise.  The equality holds by `refl` per element because the
      -- chain is all `idEquiv`/`compEquiv`/`Σ-cong-equiv-fst`/`Σ-idl-≃`
      -- whose βη-rules reduce on the pair pattern.
      composite : Σ (El 𝜏) (λ a → Σ (El (B a)) (El ∘ C a))
                ≃ Σ (Σ (El 𝜏) (El ∘ B)) (El ∘ ⅀Assoc-C' 𝜏 B C)
      composite = compEquiv (invEquiv Σ-idl-outer)
                            (Σ-cong-equiv-fst {B = El ∘ ⅀Assoc-C' 𝜏 B C} Σ-idl-inner)

      -- The composite's underlying function reduces to `(tt, b, c) ↦ ((tt, b), c)`
      -- definitionally.  ⅀Assoc≃'s function should reduce the same way, but goes
      -- through `invEquiv (Σ-cong-equiv-fst ⟦⅀⟧FS)` whose `equivCtr` produces
      -- a `transp` over a constant family that Agda doesn't auto-collapse.  We
      -- bridge by giving the second-component path as `sym (transportRefl c)`.
      composite≡⅀Assoc : composite ≡ ⅀Assoc≃ 𝜏 B C
      composite≡⅀Assoc = equivEq (funExt path)
        where
          path : (x : Σ (El 𝜏) (λ a → Σ (El (B a)) (El ∘ C a)))
               → composite .fst x ≡ ⅀Assoc≃ 𝜏 B C .fst x
          path (tt , b , c) =
            ΣPathP (refl , sym (transportRefl c))

      fst-eq : cong fst (chosen-path-id↑ B C)
             ≡ cong fst (Inj {A = ⅀ 𝜏 (λ a → ⅀ (B a) (C a))}
                              {B = ⅀ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)}
                              (⅀Assoc≃ 𝜏 B C))
      fst-eq =
          cong-∙ fst (sym (𝜏-Σ-path (λ a → ⅀ (B a) (C a))))
                      (λ i → ⅀ (𝜏-Σ-path B i) (B-path-id↑ B C i))
        ∙ cong₂ _∙_
            (cong sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                         {u = ⅀ (B tt) (C tt)}
                         {v = ⅀ 𝜏 (λ a → ⅀ (B a) (C a))}
                         (ua Σ-idl-outer)))
            (Σ-cong-equiv-fst-ua Σ-idl-inner (El ∘ ⅀Assoc-C' 𝜏 B C))
        ∙ cong (_∙ ua (Σ-cong-equiv-fst {B = El ∘ ⅀Assoc-C' 𝜏 B C} Σ-idl-inner))
               (sym (uaInvEquiv Σ-idl-outer))
        ∙ sym (uaCompEquiv (invEquiv Σ-idl-outer)
                           (Σ-cong-equiv-fst {B = El ∘ ⅀Assoc-C' 𝜏 B C} Σ-idl-inner))
        ∙ cong ua composite≡⅀Assoc
        ∙ sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                  {u = ⅀ 𝜏 (λ a → ⅀ (B a) (C a))}
                  {v = ⅀ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)}
                  (ua (⅀Assoc≃ 𝜏 B C)))

------------------------------------------------------------------------
-- sym-assoc-id↑: subst `my-PathP-id↑` along `sym-assoc-id↑-path` to
-- retype against the abstract `Inj (⅀Assoc≃ 𝜏 B C)`-index path.
------------------------------------------------------------------------
opaque
  unfolding lhs-id↑ rhs-id↑
  sym-assoc-id↑ : (B : El 𝜏 → FinSet ℓ-zero)
                  (C : (a : El 𝜏) → El (B a) → FinSet ℓ-zero)
                  (ks : (a : El 𝜏) → SymExpr (B a))
                  (kss : (a : El 𝜏) (b : El (B a)) → SymExpr (C a b))
                → PathP (λ i → SymExpr (Inj {A = ⅀ 𝜏 (λ a → ⅀ (B a) (C a))}
                                              {B = ⅀ (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)}
                                              (⅀Assoc≃ 𝜏 B C) i))
                        (sym-comp 𝜏 (λ a → ⅀ (B a) (C a)) id↑
                                  (λ a → sym-comp (B a) (C a) (ks a) (kss a)))
                        (sym-comp (⅀ 𝜏 B) (⅀Assoc-C' 𝜏 B C)
                                  (sym-comp 𝜏 B id↑ ks)
                                  (λ ab → kss _ _))
  sym-assoc-id↑ B C ks kss =
    subst (λ p → PathP (λ i → SymExpr (p i))
                       (lhs-id↑ B C ks kss) (rhs-id↑ B C ks kss))
          (sym-assoc-id↑-path B C)
          (my-PathP-id↑ B C ks kss)

------------------------------------------------------------------------
-- §C  Associativity, add↑ case.
--
-- Mirrors IExpr §10 (step A→B→C→D) but with two FinSet simplifications:
-- (1) `El (A₁ ⊎̂ A₂) = El A₁ ⊎ El A₂` lets joint-C' / joint-kss pattern
-- match on `inl`/`inr` directly (no `_≤?_`).
-- (2) `⟦⅀⟧FS = idEquiv` collapses Σ-pair forwarding to the identity, so
-- `joint-C' ∘ inl/inr` matches `⅀Assoc-C' Aᵢ ...` definitionally — the
-- joint-form bridge collapses to a single subst-filler.
------------------------------------------------------------------------

private
  -- Joint family — kept TRANSPARENT (no opaque wrap).  Uniform body via
  -- `distr-iso .fun` (which itself is uniform-Σ); reduces on `inl ab` /
  -- `inr ab` to `C (inl (fst ab)) (snd ab)` / `C (inr (fst ab)) (snd ab)`,
  -- matching `⅀Assoc-C' Aᵢ (B ∘ inl/inr) (C ∘ inl/inr) ab` after the
  -- `⟦⅀⟧FS = idEquiv` reduction.  (Opaque-wrapping joint-C' was found
  -- to block step-C-add↑'s boundary unification.)
  joint-C' : (A₁ A₂ : FinSet ℓ-zero)
             (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
             (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
           → El (⅀ A₁ (B ∘ inl) ⊎̂ ⅀ A₂ (B ∘ inr)) → FinSet ℓ-zero
  joint-C' A₁ A₂ B C ab =
    C (fst (Iso.fun (distr-iso A₁ A₂ B) ab))
      (snd (Iso.fun (distr-iso A₁ A₂ B) ab))

  joint-kss : (A₁ A₂ : FinSet ℓ-zero)
              (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
              (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
              (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
            → (ab : El (⅀ A₁ (B ∘ inl) ⊎̂ ⅀ A₂ (B ∘ inr)))
            → SymExpr (joint-C' A₁ A₂ B C ab)
  joint-kss A₁ A₂ B C kss ab =
    kss (fst (Iso.fun (distr-iso A₁ A₂ B) ab))
        (snd (Iso.fun (distr-iso A₁ A₂ B) ab))

  opaque
    unfolding ⊎̂-distr-path un
    -- B-path-add↑ via `ua-unglue` of the distr equivalence.  Body is
    -- `C (fst (ua-unglue distr i x)) (snd (ua-unglue distr i x))`.  At i=0
    -- this is `C (fst (Iso.fun distr-iso x)) (snd ...)` matching `joint-C'`.
    -- At i=1 it is `C (fst x) (snd x)` matching `⅀Assoc-C' (A₁ ⊎̂ A₂) B C`
    -- (after the `⟦⅀⟧FS = idEquiv` reduction).
    B-path-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                  (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                  (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                → PathP (λ i → El (⊎̂-distr-path A₁ A₂ B i) → FinSet ℓ-zero)
                        (joint-C' A₁ A₂ B C)
                        (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)
    B-path-add↑ A₁ A₂ B C i x =
      C (fst (ua-unglue (isoToEquiv (distr-iso A₁ A₂ B)) i x))
        (snd (ua-unglue (isoToEquiv (distr-iso A₁ A₂ B)) i x))

  opaque
    unfolding ⊎̂-distr-path un B-path-add↑
    es-path-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                   (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                   (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                   (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                 → PathP (λ i → (a : El (⊎̂-distr-path A₁ A₂ B i))
                                → SymExpr (B-path-add↑ A₁ A₂ B C i a))
                         (joint-kss A₁ A₂ B C kss)
                         (λ ab → kss (fst ab) (snd ab))
    es-path-add↑ A₁ A₂ B C kss i x =
      kss (fst (ua-unglue (isoToEquiv (distr-iso A₁ A₂ B)) i x))
          (snd (ua-unglue (isoToEquiv (distr-iso A₁ A₂ B)) i x))

  -- IH-endpoint definitions.  Opaque so the surrounding bridges don't
  -- re-expand the inner `sym-comp ∘ sym-comp` chains at every consumer.
  opaque
    Xinner-L-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                    (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                    (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                    (e₁ : SymExpr A₁)
                    (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                    (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                  → SymExpr (⅀ A₁ (λ a → ⅀ (B (inl a)) (C (inl a))))
    Xinner-L-add↑ A₁ A₂ B C e₁ ks kss =
      sym-comp A₁ (λ a → ⅀ (B (inl a)) (C (inl a))) e₁
               (λ a → sym-comp (B (inl a)) (C (inl a)) (ks (inl a)) (kss (inl a)))

    Xinner-R-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                    (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                    (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                    (e₂ : SymExpr A₂)
                    (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                    (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                  → SymExpr (⅀ A₂ (λ a → ⅀ (B (inr a)) (C (inr a))))
    Xinner-R-add↑ A₁ A₂ B C e₂ ks kss =
      sym-comp A₂ (λ a → ⅀ (B (inr a)) (C (inr a))) e₂
               (λ a → sym-comp (B (inr a)) (C (inr a)) (ks (inr a)) (kss (inr a)))

  opaque
    recL-IHend-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                      (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                      (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                      (e₁ : SymExpr A₁)
                      (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                      (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                    → SymExpr (⅀ (⅀ A₁ (B ∘ inl)) (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl)))
    recL-IHend-add↑ A₁ A₂ B C e₁ ks kss =
      sym-comp (⅀ A₁ (B ∘ inl)) (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl))
               (sym-comp A₁ (B ∘ inl) e₁ (ks ∘ inl))
               (λ ab → kss (inl (fst ab)) (snd ab))

    recR-IHend-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                      (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                      (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                      (e₂ : SymExpr A₂)
                      (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                      (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                    → SymExpr (⅀ (⅀ A₂ (B ∘ inr)) (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr)))
    recR-IHend-add↑ A₁ A₂ B C e₂ ks kss =
      sym-comp (⅀ A₂ (B ∘ inr)) (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr))
               (sym-comp A₂ (B ∘ inr) e₂ (ks ∘ inr))
               (λ ab → kss (inr (fst ab)) (snd ab))

  -- The three principal endpoints.
  opaque
    lhs-add↑ : (A₁ A₂ : FinSet ℓ-zero)
               (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
               (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
               (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
               (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
               (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
             → SymExpr (⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a)))
    lhs-add↑ A₁ A₂ B C e₁ e₂ ks kss =
      sym-comp (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a)) (add↑ e₁ e₂)
               (λ a → sym-comp (B a) (C a) (ks a) (kss a))

    rhs-add↑ : (A₁ A₂ : FinSet ℓ-zero)
               (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
               (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
               (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
               (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
               (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
             → SymExpr (⅀ (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C))
    rhs-add↑ A₁ A₂ B C e₁ e₂ ks kss =
      sym-comp (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)
               (sym-comp (A₁ ⊎̂ A₂) B (add↑ e₁ e₂) ks)
               (λ ab → kss (fst ab) (snd ab))

    joint-form-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                      (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                      (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                      (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
                      (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                      (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                    → SymExpr (⅀ (⅀ A₁ (B ∘ inl) ⊎̂ ⅀ A₂ (B ∘ inr))
                                  (joint-C' A₁ A₂ B C))
    joint-form-add↑ A₁ A₂ B C e₁ e₂ ks kss =
      sym-comp (⅀ A₁ (B ∘ inl) ⊎̂ ⅀ A₂ (B ∘ inr))
               (joint-C' A₁ A₂ B C)
               (add↑ (sym-comp A₁ (B ∘ inl) e₁ (ks ∘ inl))
                     (sym-comp A₂ (B ∘ inr) e₂ (ks ∘ inr)))
               (joint-kss A₁ A₂ B C kss)

  -- **Step A** — recipe (a) subst-filler reversal at the outer
  -- `⊎̂-distr-path A₁ A₂ (λ a → ⅀ (B a) (C a))`.
  opaque
    unfolding lhs-add↑ Xinner-L-add↑ Xinner-R-add↑
    step-A-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                  (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                  (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                  (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
                  (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                  (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                → PathP (λ i → SymExpr (sym (⊎̂-distr-path A₁ A₂
                                                (λ a → ⅀ (B a) (C a))) i))
                        (lhs-add↑ A₁ A₂ B C e₁ e₂ ks kss)
                        (add↑ (Xinner-L-add↑ A₁ A₂ B C e₁ ks kss)
                              (Xinner-R-add↑ A₁ A₂ B C e₂ ks kss))
    step-A-add↑ A₁ A₂ B C e₁ e₂ ks kss =
      symP (subst-filler SymExpr (⊎̂-distr-path A₁ A₂ (λ a → ⅀ (B a) (C a)))
                                  (add↑ (Xinner-L-add↑ A₁ A₂ B C e₁ ks kss)
                                        (Xinner-R-add↑ A₁ A₂ B C e₂ ks kss)))

  -- **Step B** — apply the per-fibre IHs underneath `add↑`.  The IHs are
  -- handed in by the top-level dispatch as recursive `sym-assoc` calls.
  opaque
    unfolding Xinner-L-add↑ Xinner-R-add↑ recL-IHend-add↑ recR-IHend-add↑
    step-B-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                  (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                  (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                  (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
                  (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                  (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                  (IH-L : PathP (λ i → SymExpr
                                          (Inj {A = ⅀ A₁ (λ a → ⅀ (B (inl a))
                                                                    (C (inl a)))}
                                                {B = ⅀ (⅀ A₁ (B ∘ inl))
                                                       (⅀Assoc-C' A₁ (B ∘ inl)
                                                                      (C ∘ inl))}
                                                (⅀Assoc≃ A₁ (B ∘ inl) (C ∘ inl)) i))
                                (Xinner-L-add↑ A₁ A₂ B C e₁ ks kss)
                                (recL-IHend-add↑ A₁ A₂ B C e₁ ks kss))
                  (IH-R : PathP (λ i → SymExpr
                                          (Inj {A = ⅀ A₂ (λ a → ⅀ (B (inr a))
                                                                    (C (inr a)))}
                                                {B = ⅀ (⅀ A₂ (B ∘ inr))
                                                       (⅀Assoc-C' A₂ (B ∘ inr)
                                                                      (C ∘ inr))}
                                                (⅀Assoc≃ A₂ (B ∘ inr) (C ∘ inr)) i))
                                (Xinner-R-add↑ A₁ A₂ B C e₂ ks kss)
                                (recR-IHend-add↑ A₁ A₂ B C e₂ ks kss))
                → PathP (λ i → SymExpr ( Inj {A = ⅀ A₁ (λ a → ⅀ (B (inl a))
                                                                  (C (inl a)))}
                                              {B = ⅀ (⅀ A₁ (B ∘ inl))
                                                     (⅀Assoc-C' A₁ (B ∘ inl)
                                                                    (C ∘ inl))}
                                              (⅀Assoc≃ A₁ (B ∘ inl) (C ∘ inl)) i
                                       ⊎̂ Inj {A = ⅀ A₂ (λ a → ⅀ (B (inr a))
                                                                  (C (inr a)))}
                                              {B = ⅀ (⅀ A₂ (B ∘ inr))
                                                     (⅀Assoc-C' A₂ (B ∘ inr)
                                                                    (C ∘ inr))}
                                              (⅀Assoc≃ A₂ (B ∘ inr) (C ∘ inr)) i))
                        (add↑ (Xinner-L-add↑ A₁ A₂ B C e₁ ks kss)
                              (Xinner-R-add↑ A₁ A₂ B C e₂ ks kss))
                        (add↑ (recL-IHend-add↑ A₁ A₂ B C e₁ ks kss)
                              (recR-IHend-add↑ A₁ A₂ B C e₂ ks kss))
    step-B-add↑ _ _ _ _ _ _ _ _ IH-L IH-R i = add↑ (IH-L i) (IH-R i)

  -- **Step C** — subst-filler over `⊎̂-distr-path (⅀ A₁ (B ∘ inl))
  -- (⅀ A₂ (B ∘ inr)) (joint-C' A₁ A₂ B C)`.  After the FinSet
  -- simplifications, the family `⅀Assoc-C' Aᵢ (B ∘ inl/inr) (C ∘ inl/inr)`
  -- IS definitionally `joint-C' A₁ A₂ B C ∘ inl/inr`, so the subst-filler
  -- terminates at `joint-form-add↑` directly (no joint-C'-on-inj bridges).
  opaque
    unfolding recL-IHend-add↑ recR-IHend-add↑ joint-form-add↑
              ⊎̂-distr-path un
    step-C-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                  (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                  (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                  (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
                  (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                  (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                → PathP (λ i → SymExpr (⊎̂-distr-path (⅀ A₁ (B ∘ inl))
                                                       (⅀ A₂ (B ∘ inr))
                                                       (joint-C' A₁ A₂ B C) i))
                        (add↑ (recL-IHend-add↑ A₁ A₂ B C e₁ ks kss)
                              (recR-IHend-add↑ A₁ A₂ B C e₂ ks kss))
                        (joint-form-add↑ A₁ A₂ B C e₁ e₂ ks kss)
    step-C-add↑ A₁ A₂ B C e₁ e₂ ks kss =
      subst-filler SymExpr (⊎̂-distr-path (⅀ A₁ (B ∘ inl))
                                          (⅀ A₂ (B ∘ inr))
                                          (joint-C' A₁ A₂ B C))
                            (add↑ (recL-IHend-add↑ A₁ A₂ B C e₁ ks kss)
                                  (recR-IHend-add↑ A₁ A₂ B C e₂ ks kss))

  -- **Step D** — `sym-comp-PathP` over the outer `⊎̂-distr-path A₁ A₂ B`
  -- with the Σ-of-paths family `B-path-add↑`.
  opaque
    unfolding joint-form-add↑ rhs-add↑ sym-comp-PathP
    step-D-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                  (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                  (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                  (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
                  (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                  (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                → PathP (λ i → SymExpr (⅀ (⊎̂-distr-path A₁ A₂ B i)
                                            (B-path-add↑ A₁ A₂ B C i)))
                        (joint-form-add↑ A₁ A₂ B C e₁ e₂ ks kss)
                        (rhs-add↑ A₁ A₂ B C e₁ e₂ ks kss)
    step-D-add↑ A₁ A₂ B C e₁ e₂ ks kss =
      sym-comp-PathP (⊎̂-distr-path A₁ A₂ B) (B-path-add↑ A₁ A₂ B C)
                     (subst-filler SymExpr (⊎̂-distr-path A₁ A₂ B)
                                            (add↑ (sym-comp A₁ (B ∘ inl) e₁ (ks ∘ inl))
                                                  (sym-comp A₂ (B ∘ inr) e₂ (ks ∘ inr))))
                     (es-path-add↑ A₁ A₂ B C kss)

  -- chosen-path-add↑ : the composed structural FinSet path, sealed
  -- independently so consumers reference it by name.
  opaque
    chosen-path-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                       (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                       (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                     → ⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a))
                     ≡ ⅀ (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)
    chosen-path-add↑ A₁ A₂ B C =
        sym (⊎̂-distr-path A₁ A₂ (λ a → ⅀ (B a) (C a)))
      ∙ (λ i → Inj {A = ⅀ A₁ (λ a → ⅀ (B (inl a)) (C (inl a)))}
                    {B = ⅀ (⅀ A₁ (B ∘ inl)) (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl))}
                    (⅀Assoc≃ A₁ (B ∘ inl) (C ∘ inl)) i
             ⊎̂ Inj {A = ⅀ A₂ (λ a → ⅀ (B (inr a)) (C (inr a)))}
                    {B = ⅀ (⅀ A₂ (B ∘ inr)) (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr))}
                    (⅀Assoc≃ A₂ (B ∘ inr) (C ∘ inr)) i)
      ∙ ⊎̂-distr-path (⅀ A₁ (B ∘ inl)) (⅀ A₂ (B ∘ inr)) (joint-C' A₁ A₂ B C)
      ∙ (λ i → ⅀ (⊎̂-distr-path A₁ A₂ B i) (B-path-add↑ A₁ A₂ B C i))

  -- composite-add↑ : the four-leg compPathP' chain.
  opaque
    unfolding chosen-path-add↑
    composite-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                     (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                     (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                     (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
                     (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                     (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                     (IH-L : PathP (λ i → SymExpr
                                            (Inj {A = ⅀ A₁ (λ a → ⅀ (B (inl a))
                                                                      (C (inl a)))}
                                                  {B = ⅀ (⅀ A₁ (B ∘ inl))
                                                         (⅀Assoc-C' A₁ (B ∘ inl)
                                                                        (C ∘ inl))}
                                                  (⅀Assoc≃ A₁ (B ∘ inl) (C ∘ inl)) i))
                                    (Xinner-L-add↑ A₁ A₂ B C e₁ ks kss)
                                    (recL-IHend-add↑ A₁ A₂ B C e₁ ks kss))
                     (IH-R : PathP (λ i → SymExpr
                                            (Inj {A = ⅀ A₂ (λ a → ⅀ (B (inr a))
                                                                      (C (inr a)))}
                                                  {B = ⅀ (⅀ A₂ (B ∘ inr))
                                                         (⅀Assoc-C' A₂ (B ∘ inr)
                                                                        (C ∘ inr))}
                                                  (⅀Assoc≃ A₂ (B ∘ inr) (C ∘ inr)) i))
                                    (Xinner-R-add↑ A₁ A₂ B C e₂ ks kss)
                                    (recR-IHend-add↑ A₁ A₂ B C e₂ ks kss))
                   → PathP (λ i → SymExpr (chosen-path-add↑ A₁ A₂ B C i))
                           (lhs-add↑ A₁ A₂ B C e₁ e₂ ks kss)
                           (rhs-add↑ A₁ A₂ B C e₁ e₂ ks kss)
    composite-add↑ A₁ A₂ B C e₁ e₂ ks kss IH-L IH-R =
      compPathP' {B = SymExpr} (step-A-add↑ A₁ A₂ B C e₁ e₂ ks kss)
        (compPathP' {B = SymExpr} (step-B-add↑ A₁ A₂ B C e₁ e₂ ks kss IH-L IH-R)
          (compPathP' {B = SymExpr} (step-C-add↑ A₁ A₂ B C e₁ e₂ ks kss)
                                     (step-D-add↑ A₁ A₂ B C e₁ e₂ ks kss)))

------------------------------------------------------------------------
-- Path-equality lemma for the add↑ case.  Identifies the four-leg
-- structural composite with `Inj (⅀Assoc≃ (A₁ ⊎̂ A₂) B C)`.  Uses the
-- `sym-idr-add↑-path` template: `Σ≡Prop-inj` + `cong-∙ fst` + per-leg
-- simplifications (`cong-fst-Σ≡Prop`, `ua-⊎`, `Σ-cong-equiv-fst-ua`) +
-- merge via `uaInvEquiv`/`uaCompEquiv` + identify composite with
-- `⅀Assoc≃` via `equivEq (funExt _)` on `inl`/`inr` cases.
------------------------------------------------------------------------
opaque
  unfolding chosen-path-add↑ B-path-add↑ ⊎̂-distr-path un

  sym-assoc-add↑-path : (A₁ A₂ : FinSet ℓ-zero)
                        (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                        (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                      → chosen-path-add↑ A₁ A₂ B C
                      ≡ Inj {A = ⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a))}
                             {B = ⅀ (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)}
                             (⅀Assoc≃ (A₁ ⊎̂ A₂) B C)
  sym-assoc-add↑-path A₁ A₂ B C =
    Σ≡Prop-inj (λ _ → isPropIsFinSet) _ _ fst-eq
    where
      -- The three distr-iso instances we use.
      distr-outer : (Σ (El A₁) (λ a → El (⅀ (B (inl a)) (C (inl a)))))
                  ⊎ (Σ (El A₂) (λ a → El (⅀ (B (inr a)) (C (inr a)))))
                  ≃ Σ (El A₁ ⊎ El A₂) (λ x → El (⅀ (B x) (C x)))
      distr-outer = isoToEquiv (distr-iso A₁ A₂ (λ a → ⅀ (B a) (C a)))

      distr-inner : (Σ (El (⅀ A₁ (B ∘ inl)))
                         (El ∘ ⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl)))
                  ⊎ (Σ (El (⅀ A₂ (B ∘ inr)))
                         (El ∘ ⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr)))
                  ≃ Σ (El (⅀ A₁ (B ∘ inl)) ⊎ El (⅀ A₂ (B ∘ inr)))
                      (El ∘ joint-C' A₁ A₂ B C)
      distr-inner = isoToEquiv (distr-iso (⅀ A₁ (B ∘ inl)) (⅀ A₂ (B ∘ inr))
                                          (joint-C' A₁ A₂ B C))

      distr-B : (Σ (El A₁) (El ∘ B ∘ inl)) ⊎ (Σ (El A₂) (El ∘ B ∘ inr))
              ≃ Σ (El A₁ ⊎ El A₂) (El ∘ B)
      distr-B = isoToEquiv (distr-iso A₁ A₂ B)

      Assoc≃-inl : El (⅀ A₁ (λ a → ⅀ (B (inl a)) (C (inl a))))
                 ≃ El (⅀ (⅀ A₁ (B ∘ inl)) (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl)))
      Assoc≃-inl = ⅀Assoc≃ A₁ (B ∘ inl) (C ∘ inl)

      Assoc≃-inr : El (⅀ A₂ (λ a → ⅀ (B (inr a)) (C (inr a))))
                 ≃ El (⅀ (⅀ A₂ (B ∘ inr)) (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr)))
      Assoc≃-inr = ⅀Assoc≃ A₂ (B ∘ inr) (C ∘ inr)

      -- Explicit composite equivalence whose action matches ⅀Assoc≃ pointwise
      -- on `inl`/`inr` cases.
      composite : El (⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a)))
                ≃ El (⅀ (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C))
      composite =
        compEquiv (invEquiv distr-outer)
        (compEquiv (⊎-equiv Assoc≃-inl Assoc≃-inr)
        (compEquiv distr-inner
                   (Σ-cong-equiv-fst {B = El ∘ ⅀Assoc-C' (A₁ ⊎̂ A₂) B C} distr-B)))

      composite≡⅀Assoc : composite ≡ ⅀Assoc≃ (A₁ ⊎̂ A₂) B C
      composite≡⅀Assoc = equivEq (funExt path)
        where
          path : (x : El (⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a))))
               → composite .fst x ≡ ⅀Assoc≃ (A₁ ⊎̂ A₂) B C .fst x
          path (inl a , b , c) = refl
          path (inr a , b , c) = refl

      -- Named per-leg paths to keep the chain readable.
      Inj-Assoc₁ : ⅀ A₁ (λ a → ⅀ (B (inl a)) (C (inl a)))
                 ≡ ⅀ (⅀ A₁ (B ∘ inl)) (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl))
      Inj-Assoc₁ = Inj {A = ⅀ A₁ (λ a → ⅀ (B (inl a)) (C (inl a)))}
                       {B = ⅀ (⅀ A₁ (B ∘ inl)) (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl))}
                       Assoc≃-inl

      Inj-Assoc₂ : ⅀ A₂ (λ a → ⅀ (B (inr a)) (C (inr a)))
                 ≡ ⅀ (⅀ A₂ (B ∘ inr)) (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr))
      Inj-Assoc₂ = Inj {A = ⅀ A₂ (λ a → ⅀ (B (inr a)) (C (inr a)))}
                       {B = ⅀ (⅀ A₂ (B ∘ inr)) (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr))}
                       Assoc≃-inr

      fst-eq : cong fst (chosen-path-add↑ A₁ A₂ B C)
             ≡ cong fst (Inj {A = ⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a))}
                              {B = ⅀ (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)}
                              (⅀Assoc≃ (A₁ ⊎̂ A₂) B C))
      fst-eq =
          -- Step 1: distribute cong fst over the 4-leg composite.
          cong-∙ fst (sym (⊎̂-distr-path A₁ A₂ (λ a → ⅀ (B a) (C a))))
                      ((λ i → Inj-Assoc₁ i ⊎̂ Inj-Assoc₂ i)
                     ∙ ⊎̂-distr-path (⅀ A₁ (B ∘ inl)) (⅀ A₂ (B ∘ inr))
                                     (joint-C' A₁ A₂ B C)
                     ∙ (λ i → ⅀ (⊎̂-distr-path A₁ A₂ B i) (B-path-add↑ A₁ A₂ B C i)))
        ∙ cong₂ _∙_
            (cong sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                         {u = ⅀ A₁ (λ a → ⅀ (B (inl a)) (C (inl a)))
                             ⊎̂ ⅀ A₂ (λ a → ⅀ (B (inr a)) (C (inr a)))}
                         {v = ⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a))}
                         (ua distr-outer)))
            (cong-∙ fst (λ i → Inj-Assoc₁ i ⊎̂ Inj-Assoc₂ i)
                         (⊎̂-distr-path (⅀ A₁ (B ∘ inl)) (⅀ A₂ (B ∘ inr))
                                        (joint-C' A₁ A₂ B C)
                       ∙ (λ i → ⅀ (⊎̂-distr-path A₁ A₂ B i)
                                  (B-path-add↑ A₁ A₂ B C i))))
        -- Now `cong fst chosen ≡ sym (ua distr-outer) ∙ (leg2 ∙ (leg3 ∙ leg4))`.
        -- Reduce leg2 = `cong fst (cong₂ _⊎̂_ Inj-Assoc₁ Inj-Assoc₂)`.
        ∙ cong (sym (ua distr-outer) ∙_)
            (cong₂ _∙_
              (λ i → cong₂ _⊎_ (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                                  {u = ⅀ A₁ (λ a → ⅀ (B (inl a)) (C (inl a)))}
                                  {v = ⅀ (⅀ A₁ (B ∘ inl))
                                          (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl))}
                                  (ua Assoc≃-inl) i)
                                (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                                  {u = ⅀ A₂ (λ a → ⅀ (B (inr a)) (C (inr a)))}
                                  {v = ⅀ (⅀ A₂ (B ∘ inr))
                                          (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr))}
                                  (ua Assoc≃-inr) i))
              (cong-∙ fst (⊎̂-distr-path (⅀ A₁ (B ∘ inl)) (⅀ A₂ (B ∘ inr))
                                          (joint-C' A₁ A₂ B C))
                            (λ i → ⅀ (⊎̂-distr-path A₁ A₂ B i)
                                     (B-path-add↑ A₁ A₂ B C i))))
        -- Apply ua-⊎ to leg2, simplify leg3 and leg4.
        ∙ cong (sym (ua distr-outer) ∙_)
            (cong₂ _∙_
              (ua-⊎ Assoc≃-inl Assoc≃-inr)
              (cong₂ _∙_
                (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                  {u = ⅀ (⅀ A₁ (B ∘ inl)) (⅀Assoc-C' A₁ (B ∘ inl) (C ∘ inl))
                      ⊎̂ ⅀ (⅀ A₂ (B ∘ inr)) (⅀Assoc-C' A₂ (B ∘ inr) (C ∘ inr))}
                  {v = ⅀ (⅀ A₁ (B ∘ inl) ⊎̂ ⅀ A₂ (B ∘ inr)) (joint-C' A₁ A₂ B C)}
                  (ua distr-inner))
                (Σ-cong-equiv-fst-ua distr-B (El ∘ ⅀Assoc-C' (A₁ ⊎̂ A₂) B C))))
        -- Merge `sym (ua distr-outer)` to `ua (invEquiv distr-outer)`.
        ∙ cong (_∙ ua (⊎-equiv Assoc≃-inl Assoc≃-inr)
                ∙ ua distr-inner
                ∙ ua (Σ-cong-equiv-fst {B = El ∘ ⅀Assoc-C' (A₁ ⊎̂ A₂) B C} distr-B))
               (sym (uaInvEquiv distr-outer))
        -- Merge all 4 `ua` legs into one via `uaCompEquiv`.
        ∙ sym ( uaCompEquiv (invEquiv distr-outer)
                  (compEquiv (⊎-equiv Assoc≃-inl Assoc≃-inr)
                             (compEquiv distr-inner
                                        (Σ-cong-equiv-fst
                                          {B = El ∘ ⅀Assoc-C' (A₁ ⊎̂ A₂) B C}
                                          distr-B)))
              ∙ cong (ua (invEquiv distr-outer) ∙_)
                  (  uaCompEquiv (⊎-equiv Assoc≃-inl Assoc≃-inr)
                       (compEquiv distr-inner
                                  (Σ-cong-equiv-fst
                                    {B = El ∘ ⅀Assoc-C' (A₁ ⊎̂ A₂) B C}
                                    distr-B))
                   ∙ cong (ua (⊎-equiv Assoc≃-inl Assoc≃-inr) ∙_)
                       (uaCompEquiv distr-inner
                          (Σ-cong-equiv-fst
                            {B = El ∘ ⅀Assoc-C' (A₁ ⊎̂ A₂) B C}
                            distr-B))))
        -- Now `cong fst chosen ≡ ua composite`.  Identify composite with ⅀Assoc≃.
        ∙ cong ua composite≡⅀Assoc
        -- Land at `cong fst (Inj (⅀Assoc≃ ...))`.
        ∙ sym (cong-fst-Σ≡Prop (λ _ → isPropIsFinSet)
                  {u = ⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a))}
                  {v = ⅀ (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)}
                  (ua (⅀Assoc≃ (A₁ ⊎̂ A₂) B C)))

------------------------------------------------------------------------
-- sym-assoc-add↑: subst `composite-add↑` along `sym-assoc-add↑-path` to
-- retype against the abstract `Inj (⅀Assoc≃ (A₁ ⊎̂ A₂) B C)` index path.
-- Takes per-fibre IHs IH-L, IH-R from the top-level dispatch.
------------------------------------------------------------------------
opaque
  unfolding lhs-add↑ rhs-add↑
  sym-assoc-add↑ : (A₁ A₂ : FinSet ℓ-zero)
                   (B : El (A₁ ⊎̂ A₂) → FinSet ℓ-zero)
                   (C : (a : El (A₁ ⊎̂ A₂)) → El (B a) → FinSet ℓ-zero)
                   (e₁ : SymExpr A₁) (e₂ : SymExpr A₂)
                   (ks : (a : El (A₁ ⊎̂ A₂)) → SymExpr (B a))
                   (kss : (a : El (A₁ ⊎̂ A₂)) (b : El (B a)) → SymExpr (C a b))
                   (IH-L : PathP (λ i → SymExpr
                                          (Inj {A = ⅀ A₁ (λ a → ⅀ (B (inl a))
                                                                    (C (inl a)))}
                                                {B = ⅀ (⅀ A₁ (B ∘ inl))
                                                       (⅀Assoc-C' A₁ (B ∘ inl)
                                                                      (C ∘ inl))}
                                                (⅀Assoc≃ A₁ (B ∘ inl) (C ∘ inl)) i))
                                  (Xinner-L-add↑ A₁ A₂ B C e₁ ks kss)
                                  (recL-IHend-add↑ A₁ A₂ B C e₁ ks kss))
                   (IH-R : PathP (λ i → SymExpr
                                          (Inj {A = ⅀ A₂ (λ a → ⅀ (B (inr a))
                                                                    (C (inr a)))}
                                                {B = ⅀ (⅀ A₂ (B ∘ inr))
                                                       (⅀Assoc-C' A₂ (B ∘ inr)
                                                                      (C ∘ inr))}
                                                (⅀Assoc≃ A₂ (B ∘ inr) (C ∘ inr)) i))
                                  (Xinner-R-add↑ A₁ A₂ B C e₂ ks kss)
                                  (recR-IHend-add↑ A₁ A₂ B C e₂ ks kss))
                 → PathP (λ i → SymExpr
                                  (Inj {A = ⅀ (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a))}
                                        {B = ⅀ (⅀ (A₁ ⊎̂ A₂) B)
                                               (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)}
                                        (⅀Assoc≃ (A₁ ⊎̂ A₂) B C) i))
                         (sym-comp (A₁ ⊎̂ A₂) (λ a → ⅀ (B a) (C a)) (add↑ e₁ e₂)
                                   (λ a → sym-comp (B a) (C a) (ks a) (kss a)))
                         (sym-comp (⅀ (A₁ ⊎̂ A₂) B) (⅀Assoc-C' (A₁ ⊎̂ A₂) B C)
                                   (sym-comp (A₁ ⊎̂ A₂) B (add↑ e₁ e₂) ks)
                                   (λ ab → kss _ _))
  sym-assoc-add↑ A₁ A₂ B C e₁ e₂ ks kss IH-L IH-R =
    subst (λ p → PathP (λ i → SymExpr (p i))
                       (lhs-add↑ A₁ A₂ B C e₁ e₂ ks kss)
                       (rhs-add↑ A₁ A₂ B C e₁ e₂ ks kss))
          (sym-assoc-add↑-path A₁ A₂ B C)
          (composite-add↑ A₁ A₂ B C e₁ e₂ ks kss IH-L IH-R)

------------------------------------------------------------------------
-- Top-level `sym-assoc`: induction on the SymExpr argument, dispatching
-- to the per-case proofs (sym-assoc-id↑ / sym-assoc-val↑ / sym-assoc-add↑).
-- The add↑ case feeds itself recursive IHs for the per-fibre half-sides,
-- via `B ∘ inl` and `B ∘ inr` restrictions (mirroring IExpr-assoc's
-- top-level dispatch at IExpr.agda:1553-1558).
--
-- Uses bare-variable patterns (not dot-patterns like `.𝜏`/`.∅̂`/`.(_⊎̂_)`)
-- because under opaque `isFinSetΣ-op` the parser interprets `.𝜏` as a
-- copattern projection (the `𝜏` field of UniverseHelpers).  Same workaround
-- as `sym-idr` at lines 459-515.
------------------------------------------------------------------------
opaque
  unfolding Xinner-L-add↑ Xinner-R-add↑ recL-IHend-add↑ recR-IHend-add↑
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
  sym-assoc _ B C id↑ ks kss = sym-assoc-id↑ B C ks kss
  sym-assoc _ B C (val↑ n) ks kss = sym-assoc-val↑ n B C ks kss
  sym-assoc _ B C (add↑ {A₁} {A₂} e₁ e₂) ks kss =
    sym-assoc-add↑ A₁ A₂ B C e₁ e₂ ks kss
      (sym-assoc A₁ (B ∘ inl) (C ∘ inl) e₁ (ks ∘ inl) (λ a → kss (inl a)))
      (sym-assoc A₂ (B ∘ inr) (C ∘ inr) e₂ (ks ∘ inr) (λ a → kss (inr a)))

SymExprOperad : SymmOperad SymExpr
Operad.isSetK SymExprOperad = isSetSymExpr
Operad.id     SymExprOperad = id↑
Operad.compₒ  SymExprOperad = sym-comp
Operad.idl    SymExprOperad = sym-idl
Operad.idr    SymExprOperad = sym-idr
Operad.assoc  SymExprOperad = sym-assoc
