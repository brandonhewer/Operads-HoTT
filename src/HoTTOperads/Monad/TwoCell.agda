{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Monad.TwoCell
--
-- 2-cell coherence of the monad `OpM O` on h-sets, with the endo-2-functor
-- and filler-uniqueness facts on h-groupoids.
--
-- The monad (1-cell) laws `join-return₁`, `join-return₂`, `join-assoc`
-- (HoTTOperads.Monad.Laws) are proved for an arbitrary carrier. Each is a
-- path in `OpM O X`, and by construction it is a *triple*: an `Index` path
-- `Inj (⅀Idl≃ _)` / `Inj (⅀Idr≃ _)` / `Inj (⅀Assoc≃ _)` in `Code`, an `Op`
-- path heterogeneous over the h-set family `K` (the operad law `idl`/`idr`/
-- `assoc`), and a `Data` path. Only the middle, `Op`, component is
-- propositional (`isPropOpPathP`: a `PathP` over the h-set family `K`); the
-- `Index` and `Data` components carry genuine content. So `operad-coherence`
-- settles the *operation* component of any coherence diagram — not a whole
-- 2-path on its own.
--
-- 2-cell coherence. The pseudomonad coherence diagrams — the associativity
-- pentagon and the unit triangles — are equalities between two parallel
-- composites of the monad-law paths, i.e. 2-paths `p ≡ q` for parallel
-- `p q : a ≡ b` in `OpM O X`. On the 2-category of **h-sets** — the setting
-- of Theorem 8.2, `OpM O` is a monad on h-sets — `OpM O X` is itself an
-- h-set (`isSetOpM`), so every hom-type `a ≡ b` is a proposition. Since
-- `isProp T` is exactly `(x y : T) → x ≡ y`, it *produces* the required
-- equality: `coherence` discharges every 2-cell coherence diagram — the
-- associativity pentagon, both unit triangles, the naturality of all three
-- structure 2-cells, and every higher diagram — and does so uniquely.
-- `unit-triangle`, `nat-left-unit`, `nat-right-unit`, `nat-assoc` record the
-- principal diagrams explicitly as concrete, well-typed 2-paths (the unit
-- triangle is genuine, not a renamed 1-law: `return <$> return y` and
-- `return (return y)` are definitionally equal, so the two unit laws inhabit
-- one common 2-path type whose two sides differ).
--
-- On h-groupoids `OpM O` is still an endo-2-functor (`isGroupoidOpM`) and
-- any two parallel coherence fillers, when they exist, are equal
-- (`coherence-unique`). Existence of the *full* h-groupoid pentagon
-- additionally needs the `Index`-component coherence: a 2-path in `Code`
-- between composites of `Inj (⅀Assoc≃ _)`. A generalised operad universe
-- (Definition 6.3) supplies for `Inj` only the 1-coherence `InjComp`; the
-- higher universe coherence the groupoid pentagon would require is the scope
-- boundary here. It is not entailed by `operad-coherence` (only the `Op`
-- third) and is not formalised in this module.
--
-- Formalises from the paper:
--   Section 8 (Monad over an Operad), Theorem 8.2 — `OpM O` is a monad on
--   h-sets; on h-sets its 2-cell coherence (associativity pentagon and unit
--   triangles) holds and is unique, as formalised below.
-- ============================================================================
module HoTTOperads.Monad.TwoCell where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso ; iso)
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Composition using (return ; join)
open import HoTTOperads.Monad.Functor using (_<$>_)
open import HoTTOperads.Monad.Laws using (join-return₁ ; join-return₂ ; join-assoc)

private
  variable
    ℓc ℓe ℓk ℓx : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk}
         (O : Operad 𝒰 K) where
  open Universe 𝒰
  open Operad O

  -- The operation component of any monad 2-cell is a proposition: a path of
  -- operations heterogeneous over an `Index`-path is a `PathP` over the
  -- h-set family `K`. (Same fact underlying
  -- HoTTOperads.Operad.HLevel.isPropOperadPathP.)
  isPropOpPathP : {I I' : Code} (q : I ≡ I') (u : K I) (v : K I')
                → isProp (PathP (λ i → K (q i)) u v)
  isPropOpPathP q u v = isOfHLevelPathP' 1 (isSetK _) u v

  -- The `Op` (operation) component of any coherence diagram commutes: two
  -- parallel operadic routes inhabiting one `PathP`-over-`K` type are equal.
  -- This settles the operation third of every monad 2-cell. The `Index` and
  -- `Data` thirds are settled by the h-set hypotheses of the next module.
  operad-coherence : {I I' : Code} (q : I ≡ I') (u : K I) (v : K I')
                     (r₁ r₂ : PathP (λ i → K (q i)) u v)
                   → r₁ ≡ r₂
  operad-coherence q u v = isPropOpPathP q u v

  -- Σ-presentation of `OpM O X`: an arity code, an operation, a decoration.
  OpMΣ : (X : Type ℓx) → Type (ℓ-max (ℓ-max ℓc ℓe) (ℓ-max ℓk ℓx))
  OpMΣ X = Σ[ I ∈ Code ] Σ[ _ ∈ K I ] (El I → X)

  OpMIsoΣ : (X : Type ℓx) → Iso (OpM O X) (OpMΣ X)
  Iso.fun (OpMIsoΣ X) (I ▷ k ▷ d) = I , k , d
  Iso.inv (OpMIsoΣ X) (I , k , d) = I ▷ k ▷ d
  Iso.rightInv (OpMIsoΣ X) _ = refl
  Iso.leftInv  (OpMIsoΣ X) _ = refl

  -- --------------------------------------------------------------------------
  -- 2-cell coherence on h-sets (Theorem 8.2: `OpM O` is a monad on h-sets).
  -- --------------------------------------------------------------------------
  module _ (sCode : isSet Code) {X : Type ℓx} (sX : isSet X) where
    -- `OpM O` preserves h-sets: a Σ of the h-set `Code`, the h-set `K I`,
    -- and the h-set `El I → X`.
    isSetOpM : isSet (OpM O X)
    isSetOpM =
      isOfHLevelRetractFromIso 2 (OpMIsoΣ X)
        (isOfHLevelΣ 2 sCode (λ I →
         isOfHLevelΣ 2 (isSetK I) (λ _ →
         isOfHLevelΠ 2 (λ _ → sX))))

    -- Total 2-cell coherence. Every hom-type of the h-set `OpM O X` is a
    -- proposition, and `isProp T = (x y : T) → x ≡ y` *produces* the
    -- equality. Hence every pseudomonad coherence diagram — the
    -- associativity pentagon, both unit triangles, the naturality of each
    -- structure 2-cell, and every higher diagram — is an instance of
    -- `coherence`, and is moreover unique.
    coherence : {x y : OpM O X} (p q : x ≡ y) → p ≡ q
    coherence {x = x} {y = y} = isSetOpM x y

    -- The monad (1-cell) laws at the h-set carrier, re-exported from
    -- HoTTOperads.Monad.Laws. These are the 1-cells of the monad, *not* the
    -- 2-cell coherence; the coherence between them is `coherence` and the
    -- named diagrams below.
    monad-left-unit : (x : OpM O X) → join O (return O x) ≡ x
    monad-left-unit = join-return₁ O

    monad-right-unit : (x : OpM O X) → join O (return O <$> x) ≡ x
    monad-right-unit = join-return₂ O

    monad-assoc : (y : OpM O (OpM O (OpM O X)))
                → join O (join O y) ≡ join O ((join O) <$> y)
    monad-assoc = join-assoc O

    -- Unit triangle: the two unit laws agree at the unit. `return <$>
    -- return y` and `return (return y)` are definitionally equal, so both
    -- `join-return₁ O (return O y)` and `join-return₂ O (return O y)`
    -- inhabit `join O (return O (return O y)) ≡ return O y`; the triangle is
    -- the equality of these two distinct parallel routes (a genuine 2-path,
    -- not a renamed 1-law).
    unit-triangle : (y : X)
                  → join-return₁ O (return O y) ≡ join-return₂ O (return O y)
    unit-triangle y = coherence (join-return₁ O (return O y))
                                (join-return₂ O (return O y))

    -- Naturality of the left-unit 2-cell `join ∘ return ⇒ id`: the square
    -- relating `join-return₁` along a path `p` commutes.
    nat-left-unit : {x y : OpM O X} (p : x ≡ y)
                  → cong (λ z → join O (return O z)) p ∙ join-return₁ O y
                  ≡ join-return₁ O x ∙ p
    nat-left-unit p = coherence _ _

    -- Naturality of the right-unit 2-cell `join ∘ (return <$>_) ⇒ id`.
    nat-right-unit : {x y : OpM O X} (p : x ≡ y)
                   → cong (λ z → join O (return O <$> z)) p ∙ join-return₂ O y
                   ≡ join-return₂ O x ∙ p
    nat-right-unit p = coherence _ _

    -- Naturality of the associativity 2-cell: the associativity-coherence
    -- square (the content of the monad pentagon) commutes.
    nat-assoc : {y y' : OpM O (OpM O (OpM O X))} (p : y ≡ y')
              → cong (λ z → join O (join O z)) p ∙ join-assoc O y'
              ≡ join-assoc O y ∙ cong (λ z → join O ((join O) <$> z)) p
    nat-assoc p = coherence _ _

  -- --------------------------------------------------------------------------
  -- h-groupoids: `OpM O` is an endo-2-functor and coherence fillers, when
  -- they exist, are unique. (Existence of the full h-groupoid pentagon is
  -- the scope boundary noted in the header.)
  -- --------------------------------------------------------------------------
  module _ (gCode : isGroupoid Code) {X : Type ℓx} (gX : isGroupoid X) where
    -- `OpM O` preserves h-groupoids: a Σ of the h-groupoid `Code`, the
    -- h-set `K I` (raised to an h-groupoid), and the h-groupoid `El I → X`.
    -- So `OpM O` is an endo-2-functor on the 2-category of h-groupoids.
    isGroupoidOpM : isGroupoid (OpM O X)
    isGroupoidOpM =
      isOfHLevelRetractFromIso 3 (OpMIsoΣ X)
        (isOfHLevelΣ 3 gCode (λ I →
         isOfHLevelΣ 3 (isOfHLevelSuc 2 (isSetK I)) (λ _ →
         isOfHLevelΠ 3 (λ _ → gX))))

    -- Between any two parallel monad 2-cells the space of fillers is a
    -- proposition: whenever a coherence 2-path exists, it is unique.
    coherence-unique : {x y : OpM O X} (p q : x ≡ y) → isProp (p ≡ q)
    coherence-unique {x = x} {y = y} = isGroupoidOpM x y
