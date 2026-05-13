{-# OPTIONS --cubical #-}
module HoTTOperads.Universe.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Sigma.Properties using (Σ-assoc-≃ ; Σ-cong-equiv-fst ; Σ-cong-equiv-snd)
open import Cubical.Data.Unit using (Unit ; tt)

private
  variable
    ℓ : Level

-- Metatheoretic Σ identity/associativity equivalences used to derive the canonical universe equivalences.
-- NOTE: kept transparent — invEq-⅀Idl / invEq-⅀Idr below need their iso-bodies to reduce
-- for `cong tail (secEq …) : equivFun (⅀Idl≃ A) x ≡ b` to typecheck.

Σ-idl-≃ : {A : Unit → Type ℓ} → A tt ≃ (Σ Unit A)
Σ-idl-≃ {A = A} = isoToEquiv (iso (λ a → tt , a) (λ p → snd p)
                                  (λ _ → refl) (λ _ → refl))

Σ-idr-≃ : {A : Type ℓ} → (Σ[ _ ∈ A ] Unit) ≃ A
Σ-idr-≃ = isoToEquiv (iso fst (λ a → a , tt) (λ _ → refl) (λ _ → refl))

-- Step 1: the base universe structure (without the three coherence laws).
record UniverseBase (ℓc ℓe : Level) : Type (ℓ-suc (ℓ-max ℓc ℓe)) where
  field
    Code : Type ℓc
    El   : Code → Type ℓe
    ⅀    : (A : Code) → (El A → Code) → Code
    𝜏    : Code
    ⟦⅀⟧  : (A : Code) (B : El A → Code) → El (⅀ A B) ≃ (Σ[ a ∈ El A ] El (B a))
    ⟦𝜏⟧  : El 𝜏 ≃ Unit
    Inj  : {A B : Code} → El A ≃ El B → A ≡ B
    InjComp : {A B C : Code}
              (e₁ : El A ≃ El B) (e₂ : El B ≃ El C)
            → Inj (compEquiv e₁ e₂) ≡ Inj e₁ ∙ Inj e₂

  -- Canonical derived equivalences on underlying types.
  ⅀Idl≃ : (A : Code) → El (⅀ 𝜏 (λ _ → A)) ≃ El A
  ⅀Idl≃ A = compEquiv (⟦⅀⟧ 𝜏 (λ _ → A))
            (compEquiv (Σ-cong-equiv-fst ⟦𝜏⟧) (invEquiv Σ-idl-≃))

  ⅀Idr≃ : (A : Code) → El (⅀ A (λ _ → 𝜏)) ≃ El A
  ⅀Idr≃ A = compEquiv (⟦⅀⟧ A (λ _ → 𝜏))
            (compEquiv (Σ-cong-equiv-snd (λ _ → ⟦𝜏⟧)) Σ-idr-≃)

  ⅀Assoc-C' : (A : Code) (B : El A → Code)
              (C : (a : El A) → El (B a) → Code)
            → El (⅀ A B) → Code
  ⅀Assoc-C' A B C ab = C (fst (equivFun (⟦⅀⟧ A B) ab))
                         (snd (equivFun (⟦⅀⟧ A B) ab))

  ⅀Assoc≃ : (A : Code) (B : El A → Code)
            (C : (a : El A) → El (B a) → Code)
          → El (⅀ A (λ a → ⅀ (B a) (C a)))
          ≃ El (⅀ (⅀ A B) (⅀Assoc-C' A B C))
  ⅀Assoc≃ A B C =
    compEquiv (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
    (compEquiv (Σ-cong-equiv-snd (λ a → ⟦⅀⟧ (B a) (C a)))
    (compEquiv (invEquiv (Σ-assoc-≃ {A = El A} {B = λ a → El (B a)}
                                    {C = λ a b → El (C a b)}))
    (compEquiv
      (invEquiv (Σ-cong-equiv-fst {B = λ ab → El (C (fst ab) (snd ab))} (⟦⅀⟧ A B)))
      (invEquiv (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C))))))

  -- Canonical pre-images for ⅀Idl≃, ⅀Idr≃, ⅀Assoc≃: the explicit "unfolded" form
  -- agrees (propositionally) with the abstract invEq of the composite equivalence.
  -- Proofs go via uniqueness of inverses: if equivFun e x ≡ b then x ≡ invEq e b.
  -- For each lemma, the relevant secEq is the only propositional step; the rest
  -- of the chain is definitional thanks to η on Σ, isoToEquiv reducing invEq to
  -- Iso.inv, and invEq (invEquiv e) reducing to equivFun e.

  opaque
    invEq-⅀Idl : (A : Code) (b : El A)
               → invEq (⟦⅀⟧ 𝜏 (λ _ → A)) (invEq ⟦𝜏⟧ tt , b) ≡ invEq (⅀Idl≃ A) b
    invEq-⅀Idl A b =
      sym (retEq (⅀Idl≃ A) x) ∙ cong (invEq (⅀Idl≃ A)) p
      where
        x : El (⅀ 𝜏 (λ _ → A))
        x = invEq (⟦⅀⟧ 𝜏 (λ _ → A)) (invEq ⟦𝜏⟧ tt , b)
        tail : Σ[ _ ∈ El 𝜏 ] El A → El A
        tail y = invEq (Σ-idl-≃ {A = λ _ → El A})
                       (equivFun (Σ-cong-equiv-fst {B = λ _ → El A} ⟦𝜏⟧) y)
        p : equivFun (⅀Idl≃ A) x ≡ b
        p = cong tail (secEq (⟦⅀⟧ 𝜏 (λ _ → A)) (invEq ⟦𝜏⟧ tt , b))

    invEq-⅀Idr : (A : Code) (a : El A)
               → invEq (⟦⅀⟧ A (λ _ → 𝜏)) (a , invEq ⟦𝜏⟧ tt) ≡ invEq (⅀Idr≃ A) a
    invEq-⅀Idr A a =
      sym (retEq (⅀Idr≃ A) x) ∙ cong (invEq (⅀Idr≃ A)) p
      where
        x : El (⅀ A (λ _ → 𝜏))
        x = invEq (⟦⅀⟧ A (λ _ → 𝜏)) (a , invEq ⟦𝜏⟧ tt)
        tail : Σ[ _ ∈ El A ] El 𝜏 → El A
        tail y = equivFun (Σ-idr-≃ {A = El A})
                          (equivFun (Σ-cong-equiv-snd (λ _ → ⟦𝜏⟧)) y)
        p : equivFun (⅀Idr≃ A) x ≡ a
        p = cong tail (secEq (⟦⅀⟧ A (λ _ → 𝜏)) (a , invEq ⟦𝜏⟧ tt))

-- Step 2: the coherence predicate over a UniverseBase.
record UniverseCoh {ℓc ℓe : Level} (𝒰 : UniverseBase ℓc ℓe) : Type (ℓ-suc (ℓ-max ℓc ℓe)) where
  open UniverseBase 𝒰
  field
    ⟦⅀Idl⟧ : (A : Code) → ua (⅀Idl≃ A) ≡ cong El (Inj (⅀Idl≃ A))
    ⟦⅀Idr⟧ : (A : Code) → ua (⅀Idr≃ A) ≡ cong El (Inj (⅀Idr≃ A))
    ⟦⅀Assoc⟧ : (A : Code) (B : El A → Code)
               (C : (a : El A) → El (B a) → Code)
             → ua (⅀Assoc≃ A B C)
             ≡ cong El (Inj {A = ⅀ A (λ a → ⅀ (B a) (C a))}
                            {B = ⅀ (⅀ A B) (⅀Assoc-C' A B C)}
                            (⅀Assoc≃ A B C))

-- Step 3: the full Universe is a base plus coherences.
record Universe (ℓc ℓe : Level) : Type (ℓ-suc (ℓ-max ℓc ℓe)) where
  field
    base : UniverseBase ℓc ℓe
    coh  : UniverseCoh base

  open UniverseBase base public
  open UniverseCoh  coh  public

-- Paper notation: ⟦ 𝒰 ∋ A ⟧ for the interpretation of code A in universe 𝒰.
⟦_∋_⟧ : ∀ {ℓc ℓe} (𝒰 : Universe ℓc ℓe) → Universe.Code 𝒰 → Type ℓe
⟦ 𝒰 ∋ A ⟧ = Universe.El 𝒰 A

-- Convenience accessors so `Universe.⅀Idl≃ 𝒰 A` style works without recourse to base.
module UniverseHelpers {ℓc ℓe : Level} (𝒰 : Universe ℓc ℓe) where
  open Universe 𝒰 public

