{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Small.Properties where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.FinSet.Properties hiding (_/_)
open import Operad.FinSet.Product
open import Operad.FinSet.Function
open import Operad.FinSet.Small.Base
open import Operad.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    U : Type ℓ₁
    P : U → Type ℓ₂

open Iso

FinSetD : ∀ ℓ → Type (ℓ-suc ℓ)
FinSetD ℓ = FinClosure {ℓ₂ = ℓ} ⟦_⟧

ΣIdL : (A : FinClosure P) → ΣF ⊤F (λ _ → A) ≡ A
ΣIdL A = un _ _ (isoToEquiv Σ-Idl)

ΣIdR : (A : FinClosure P) → ΣF A (λ _ → ⊤F) ≡ A
ΣIdR A = un _ _ (isoToEquiv Σ-Idr)

ΣAssoc : (A : FinClosure P) (B : El A → FinClosure P)
         (C : ∀ a → El (B a) → FinClosure P) →
         ΣF (ΣF A B) (uncurry C) ≡ ΣF A λ a → ΣF (B a) (C a)
ΣAssoc A B C = un _ _ (isoToEquiv Σ-assoc-Iso)

_/_ : (A : FinClosure P) (a : El A) → FinClosure P
A / a = ΣF A (¬F ∘ ≡F A a)

record FinClosed {U : Type ℓ₁}
                 (P : U → Type ℓ₂)
                 (F : Type ℓ₂ → Type ℓ₃) : Type (ℓ-suc (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃))) where
  field
    isPropF : ∀ x → isProp (F x)
    Ty-F    : ∀ u → F (P u)
    ⊥-F     : F (Lift (Fin 0))
    ⊤-F     : F (Lift (Fin 1))
    Σ-F     : ∀ {A B} → F A → (∀ a → F (B a)) → F (Σ A B)
    Π-F     : ∀ {A} {B : A → Type ℓ₂} → F A → (∀ a → F (B a)) → F (∀ a → B a)
    ≡-F     : ∀ {A} → F A → (a b : A) → F (a ≡ b)
    ¬-F     : ∀ {A} → F A → F (¬ A)

open FinClosed

fromClosed : {F : Type ℓ₂ → Type ℓ₃} →
             FinClosed P F → ∀ A → F (El {P = P} A)
fromClosed p (Ty u)           = Ty-F p u
fromClosed p ⊥F               = ⊥-F p
fromClosed p ⊤F               = ⊤-F p
fromClosed p (ΣF A B)         = Σ-F p (fromClosed p A) (fromClosed p ∘ B)
fromClosed p (ΠF A B)         = Π-F p (fromClosed p A) (fromClosed p ∘ B)
fromClosed p (≡F A a b)       = ≡-F p (fromClosed p A) a b
fromClosed p (¬F A)           = ¬-F p (fromClosed p A)
fromClosed p (un A₁ A₂ eq i)  =
  isProp→PathP (λ i → isPropF p (ua eq i))
               (fromClosed p A₁)
               (fromClosed p A₂) i

open Iso

module _ {U : Type ℓ₁} {P : U → Type ℓ₂} {F : Type ℓ₂ → Type ℓ₃} where

  open import Cubical.Foundations.Univalence.Universe (FinClosure P) El un (λ _ → refl)

  reflectIso : (F→U : ∀ A → F A → U) →
               (∀ A FA → P (F→U A FA) ≃ A) →
               FinClosed P F →
               Iso (FinClosure P) (Σ[ A ∈ Type ℓ₂ ] F A)
  fun      (reflectIso F→U F→U→P C) A        = El A , fromClosed C A
  inv      (reflectIso F→U F→U→P C) (A , FA) = Ty (F→U A FA)
  rightInv (reflectIso F→U F→U→P C) (A , FA) = Σ≡Prop (isPropF C) (ua (F→U→P A FA))
  leftInv  (reflectIso F→U F→U→P C) A        =
    un (Ty (F→U (El A) (fromClosed C A))) A
       (F→U→P (El A) (fromClosed C A))

isFinSetFinClosed : FinClosed {ℓ₂ = ℓ₂} ⟦_⟧ isFinite
isPropF  isFinSetFinClosed _ = isPropIsFinite
Ty-F     isFinSetFinClosed   = snd
⊥-F      isFinSetFinClosed   = isFinite-n 0
⊤-F      isFinSetFinClosed   = isFinite-n 1
Σ-F      isFinSetFinClosed   = isFiniteΣ
Π-F      isFinSetFinClosed   = isFiniteΠ
≡-F      isFinSetFinClosed   = isFiniteFin≡
¬-F      isFinSetFinClosed   = isFinite¬

FinSet↔FinSetD : ∀ ℓ → Iso (FinSetD ℓ) (FinSet ℓ)
FinSet↔FinSetD ℓ = reflectIso _,_ (λ _ _ → idEquiv _) isFinSetFinClosed
