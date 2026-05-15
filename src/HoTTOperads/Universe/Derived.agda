{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Universe.Derived
--
-- Derived data and coherence lemmas for any `Universe`: path-valued forms of
-- the canonical equivalences (⅀Idl, ⅀Idr, ⅀Assoc via Inj), the two `Inj`
-- coherence lemmas, and supporting h-prop facts about El 𝜏 / El (⅀ 𝜏 𝜏).
--
-- Formalises from the paper (Section 6, Generalised Operad Universes):
--   Proposition 6.1 — `InjRefl`
--   Proposition 6.2 — `InjSec`
-- Plus derived path/h-prop infrastructure for Definition 6.3 used
-- throughout the rest of the library.
-- ============================================================================
module HoTTOperads.Universe.Derived where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels using (isOfHLevelRespectEquiv ; isPropΣ)
open import Cubical.Foundations.GroupoidLaws using (lCancel ; lUnit ; rUnit ; assoc)
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma using (Σ-syntax ; _×_ ; _,_ ; fst ; snd)
open import Cubical.Data.Sigma.Properties using (Σ-cong-equiv-snd)
open import Cubical.Data.Unit using (Unit ; tt ; isPropUnit)

open import HoTTOperads.Universe.Base

private
  variable
    ℓ ℓ' ℓc ℓe : Level

opaque
  -- Any two equivalences between propositions are propositionally equal.
  propEquivEq : {X : Type ℓ} {Y : Type ℓ'} → isProp X → isProp Y
              → (e₁ e₂ : X ≃ Y) → e₁ ≡ e₂
  propEquivEq _ pY e₁ e₂ = equivEq (funExt (λ _ → pY _ _))

  -- Σ-cong-equiv-snd of the all-identity-equivalence family is the identity.
  Σ-cong-equiv-snd-id : {A : Type ℓ} {B : A → Type ℓ'}
                      → Σ-cong-equiv-snd (λ a → idEquiv (B a)) ≡ idEquiv (Σ[ a ∈ A ] B a)
  Σ-cong-equiv-snd-id = equivEq refl

module _ {ℓc ℓe : Level} (𝒰 : Universe ℓc ℓe) where
  open Universe 𝒰

  -- Path-valued versions of the canonical equivalences (via Inj).
  ⅀Idl : (A : Code) → ⅀ 𝜏 (λ _ → A) ≡ A
  ⅀Idl A = Inj (⅀Idl≃ A)

  ⅀Idr : (A : Code) → ⅀ A (λ _ → 𝜏) ≡ A
  ⅀Idr A = Inj (⅀Idr≃ A)

  ⅀Assoc : (A : Code) (B : El A → Code)
           (C : (a : El A) → El (B a) → Code)
         → ⅀ A (λ a → ⅀ (B a) (C a)) ≡ ⅀ (⅀ A B) (⅀Assoc-C' A B C)
  ⅀Assoc A B C = Inj (⅀Assoc≃ A B C)

  opaque
    -- "p ≡ p ∙ p" implies "p ≡ refl" in any path groupoid.
    idem→refl : {X : Type ℓc} {x : X} (p : x ≡ x) → p ≡ p ∙ p → p ≡ refl
    idem→refl p step =
      p                         ≡⟨ lUnit p ⟩
      refl ∙ p                  ≡⟨ cong (_∙ p) (sym (lCancel p)) ⟩
      (sym p ∙ p) ∙ p           ≡⟨ sym (assoc (sym p) p p) ⟩
      sym p ∙ (p ∙ p)           ≡⟨ cong (sym p ∙_) (sym step) ⟩
      sym p ∙ p                 ≡⟨ lCancel p ⟩
      refl                      ∎

    -- Proposition 6.1 (Section 6, Generalised Operad Universes).
    -- Inj sends the identity equivalence to refl.
    InjRefl : (A : Code) → Inj (idEquiv (El A)) ≡ refl
    InjRefl A =
      let e = idEquiv (El A)
          p = Inj e
          comp-id-id : compEquiv e e ≡ e
          comp-id-id = equivEq refl
          step : p ≡ p ∙ p
          step = sym (cong Inj comp-id-id) ∙ InjComp e e
      in idem→refl p step

    -- Inj of an inverse equivalence is the symmetric of Inj.
    InjInv : {A B : Code} (e : El A ≃ El B) → Inj (invEquiv e) ≡ sym (Inj e)
    InjInv {A = A} {B = B} e =
        Inj (invEquiv e)                       ≡⟨ lUnit _ ⟩
        refl ∙ Inj (invEquiv e)                ≡⟨ cong (_∙ Inj (invEquiv e)) (sym (lCancel (Inj e))) ⟩
        (sym (Inj e) ∙ Inj e) ∙ Inj (invEquiv e)
                                                ≡⟨ sym (assoc (sym (Inj e)) (Inj e) (Inj (invEquiv e))) ⟩
        sym (Inj e) ∙ (Inj e ∙ Inj (invEquiv e))
                                                ≡⟨ cong (sym (Inj e) ∙_) collapse ⟩
        sym (Inj e) ∙ refl                     ≡⟨ sym (rUnit (sym (Inj e))) ⟩
        sym (Inj e)                            ∎
      where
        collapse : Inj e ∙ Inj (invEquiv e) ≡ refl
        collapse = sym (InjComp e (invEquiv e))
                 ∙ cong Inj (invEquiv-is-rinv e)
                 ∙ InjRefl A

    -- Proposition 6.2 (Section 6, Generalised Operad Universes).
    -- Every path in `Code` is recovered as `Inj` of the corresponding
    -- equivalence. Proof by path induction: at refl, `cong El refl` is refl,
    -- pathToEquiv refl ≡ idEquiv, so Inj (pathToEquiv (cong El refl)) ≡
    -- Inj (idEquiv) ≡ refl by InjRefl.
    InjSec : {A B : Code} (p : A ≡ B) → Inj (pathToEquiv (cong El p)) ≡ p
    InjSec {A = A} = J (λ B' p' → Inj (pathToEquiv (cong El p')) ≡ p')
                       (cong Inj pathToEquivRefl ∙ InjRefl A)

  opaque
    -- El 𝜏 is a proposition: it is equivalent to Unit.
    isPropEl𝜏 : isProp (El 𝜏)
    isPropEl𝜏 = isOfHLevelRespectEquiv 1 (invEquiv ⟦𝜏⟧) isPropUnit

    -- El (⅀ 𝜏 (λ _ → 𝜏)) is a proposition: it is equivalent to Σ El𝜏 (λ _ → El𝜏).
    isPropEl-⅀𝜏𝜏 : isProp (El (⅀ 𝜏 (λ _ → 𝜏)))
    isPropEl-⅀𝜏𝜏 = isOfHLevelRespectEquiv 1 (invEquiv (⟦⅀⟧ 𝜏 (λ _ → 𝜏)))
                                            (isPropΣ isPropEl𝜏 (λ _ → isPropEl𝜏))

  opaque
    -- ⟦⅀⟧-naturality in second argument: the transport along cong (El ∘ ⅀ A) q
    -- factors as ⟦⅀⟧ ⨟ Σ-cong-equiv-snd (pointwise transport) ⨟ invEquiv ⟦⅀⟧.
    -- Provable by path induction: at q = refl, both sides are idEquiv
    -- via pathToEquivRefl, Σ-cong-equiv-snd-id, and invEquiv-is-rinv on ⟦⅀⟧.
    ⟦⅀⟧-natural-snd : (A : Code) {B₁ B₂ : El A → Code} (q : B₁ ≡ B₂)
                    → pathToEquiv (cong (λ B → El (⅀ A B)) q)
                    ≡ compEquiv (⟦⅀⟧ A B₁)
                                (compEquiv (Σ-cong-equiv-snd
                                              (λ a → pathToEquiv (cong El (funExt⁻ q a))))
                                           (invEquiv (⟦⅀⟧ A B₂)))
    ⟦⅀⟧-natural-snd A {B₁} =
      J (λ B₂ q → pathToEquiv (cong (λ B → El (⅀ A B)) q)
                ≡ compEquiv (⟦⅀⟧ A B₁)
                            (compEquiv (Σ-cong-equiv-snd {A = El A}
                                          {B = λ a → El (B₁ a)} {B' = λ a → El (B₂ a)}
                                          (λ a → pathToEquiv (cong El (funExt⁻ q a))))
                                       (invEquiv (⟦⅀⟧ A B₂))))
        base-refl
      where
        -- At q = refl, LHS = pathToEquiv refl = idEquiv. RHS = ⟦⅀⟧ ⨟ idEquiv ⨟ invEquiv ⟦⅀⟧
        -- = ⟦⅀⟧ ⨟ invEquiv ⟦⅀⟧ = idEquiv (by invEquiv-is-rinv).
        base-refl : pathToEquiv (cong (λ B → El (⅀ A B)) (refl {x = B₁}))
                  ≡ compEquiv (⟦⅀⟧ A B₁)
                              (compEquiv (Σ-cong-equiv-snd {A = El A}
                                            {B = λ a → El (B₁ a)} {B' = λ a → El (B₁ a)}
                                            (λ a → pathToEquiv (cong El (funExt⁻ (refl {x = B₁}) a))))
                                         (invEquiv (⟦⅀⟧ A B₁)))
        base-refl =
            pathToEquiv (cong (λ B → El (⅀ A B)) (refl {x = B₁}))
          ≡⟨ pathToEquivRefl ⟩
            idEquiv (El (⅀ A B₁))
          ≡⟨ sym (invEquiv-is-rinv (⟦⅀⟧ A B₁)) ⟩
            compEquiv (⟦⅀⟧ A B₁) (invEquiv (⟦⅀⟧ A B₁))
          ≡⟨ cong (compEquiv (⟦⅀⟧ A B₁)) (sym (compEquivIdEquiv (invEquiv (⟦⅀⟧ A B₁)))) ⟩
            compEquiv (⟦⅀⟧ A B₁) (compEquiv (idEquiv _) (invEquiv (⟦⅀⟧ A B₁)))
          ≡⟨ cong (λ e → compEquiv (⟦⅀⟧ A B₁) (compEquiv e (invEquiv (⟦⅀⟧ A B₁))))
                  (sym (Σ-cong-equiv-snd-id {A = El A} {B = λ a → El (B₁ a)})) ⟩
            compEquiv (⟦⅀⟧ A B₁)
                      (compEquiv (Σ-cong-equiv-snd {A = El A}
                                    {B = λ a → El (B₁ a)} {B' = λ a → El (B₁ a)}
                                    (λ a → idEquiv (El (B₁ a))))
                                 (invEquiv (⟦⅀⟧ A B₁)))
          ≡⟨ cong (λ f → compEquiv (⟦⅀⟧ A B₁)
                         (compEquiv (Σ-cong-equiv-snd {A = El A}
                                       {B = λ a → El (B₁ a)} {B' = λ a → El (B₁ a)} f)
                                    (invEquiv (⟦⅀⟧ A B₁))))
                  (funExt (λ a → sym (pathToEquivRefl {A = El (B₁ a)}))) ⟩
            compEquiv (⟦⅀⟧ A B₁)
                      (compEquiv (Σ-cong-equiv-snd {A = El A}
                                    {B = λ a → El (B₁ a)} {B' = λ a → El (B₁ a)}
                                    (λ a → pathToEquiv (cong El (funExt⁻ (refl {x = B₁}) a))))
                                 (invEquiv (⟦⅀⟧ A B₁)))
          ∎
