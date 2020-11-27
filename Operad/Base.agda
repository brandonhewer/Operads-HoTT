{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Base where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Cubical.Relation.Nullary hiding (⟪_⟫)

open import Operad.Fin
open import Operad.FinSet
open import Operad.Species

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    A : Type ℓ₁
    B : A → Type ℓ₂
    C : ∀ a → B a → Type ℓ₃
    D : ∀ a b → C a b → Type ℓ₄
    E : ∀ a b c → D a b c → Type ℓ₅

  Comp : (FinSet ℓ₁ → Type ℓ₂) → (A : FinSet ℓ₁) (B : ⟦ A ⟧ → FinSet ℓ₁) → Type _
  Comp K A B = K A → (bs : (a : ⟦ A ⟧) → K (B a)) → K (Σⁿ A B)

  open Iso

  Fin0↔a≢b : ∀ {ℓ₁} {A : Type ℓ₁} {a b : A} → a ≡ b → Iso (Fin 0) (¬ (a ≡ b))
  fun      (Fin0↔a≢b p) ()
  inv      (Fin0↔a≢b p) ¬p = ⊥-rec (¬p p)
  rightInv (Fin0↔a≢b p) ¬p = ⊥-rec (¬p p)
  leftInv  (Fin0↔a≢b p) ()

  Fin1↔a≢b : ∀ {ℓ₁} {A : Type ℓ₁} {a b : A} → ¬ (a ≡ b) → Iso (Fin 1) (¬ (a ≡ b))
  fun      (Fin1↔a≢b ¬p) zero = ¬p
  inv      (Fin1↔a≢b ¬p) _    = zero
  rightInv (Fin1↔a≢b ¬p) ¬q   = isProp¬ _ _ _
  leftInv  (Fin1↔a≢b ¬p) zero = refl

record Operad (ℓ₁ ℓ₂ : Level) : Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂)) where
  field
    K      : Species 2 ℓ₁ ℓ₂
    id     : typ (K (⊤-FinSet ℓ₁))
    comp   : ∀ A B → Comp (typ ∘ K) A B
    idl′   : ∀ n k →
               subst (typ ∘ K) Σⁿ-Idl (comp (⊤-FinSet ℓ₁) (λ _ → n-FinSet n) id (λ _ → k))
               ≡ k
    idr′   : ∀ n k →
               subst (typ ∘ K) Σⁿ-Idr (comp (n-FinSet n) (λ _ → ⊤-FinSet ℓ₁) k λ _ → id)
               ≡ k
    assoc′ : ∀ n (ns : Fin n → ℕ) (nss : (i : Fin n) → Fin (ns i) → ℕ) k ks kss →
               let A     = n-FinSet n
                   B     = n-FinSet ∘ ns ∘ lower
                   C i j = n-FinSet (nss (lower i) (lower j))
                in subst (typ ∘ K) (Σⁿ-Assoc A B C)
                     (comp (Σⁿ A B) (uncurry C) (comp A B k ks) (uncurry kss))
                   ≡ (comp A (λ a → Σⁿ (B a) (C a)) k λ a → comp (B a) (C a) (ks a) (kss a))

  Ops : FinSet ℓ₁ → Type ℓ₂
  Ops = typ ∘ K

  isSetOps : ∀ A → isSet (Ops A)
  isSetOps = str ∘ K

  apply : (A : FinSet ℓ₁) (a : ⟦ A ⟧) → Ops A → Ops (⊥-FinSet ℓ₁) → Ops (A / a)
  apply A a f x = subst Ops (Lift≡ _ _ refl) (comp A (A ⟨ a ≢_⟩) f fs)
    where
      fs : ∀ b → Ops (A ⟨ a ≢ b ⟩)
      fs b with isDiscreteFinSet A a b
      ... | yes p = subst Ops (Lift≡ _ _ (isoToPath (compIso (invIso LiftIso) (Fin0↔a≢b p)))) x
      ... | no ¬p = subst Ops (Lift≡ _ _ (isoToPath (compIso (invIso LiftIso) (Fin1↔a≢b ¬p)))) id

  idl : ∀ A k → subst Ops Σⁿ-Idl (comp (⊤-FinSet ℓ₁) (λ _ → A) id λ _ → k) ≡ k
  idl = finiteProp (λ A → ∀ k → _) (λ _ → isPropΠ λ _ → isSetOps _ _ _) idl′          

  idr : ∀ A k → subst Ops Σⁿ-Idr (comp A (λ _ → ⊤-FinSet ℓ₁) k λ _ → id) ≡ k
  idr = finiteProp (λ A → ∀ k → _) (λ _ → isPropΠ λ _ → isSetOps _ _ _) idr′

  assoc : ∀ A B C k ks kss →
            subst Ops (Σⁿ-Assoc A B C)
                      (comp (Σⁿ A B) (uncurry C) (comp A B k ks) (uncurry kss))
            ≡ (comp A (λ a → Σⁿ (B a) (C a)) k λ a → comp (B a) (C a) (ks a) (kss a))
  assoc = finiteProp₃
            (λ A B C → ∀ k ks kss → _)
            (λ _ _ _ → isPropΠ3 λ _ _ _ → isSetOps _ _ _)
            assoc′
