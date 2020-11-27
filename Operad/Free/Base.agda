{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Free.Base where

open import Cubical.Data.Nat

open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Transport

open import Operad.Base
open import Operad.Fin
open import Operad.FinSet
open import Operad.Morphism
open import Operad.Species

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level

{-

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

-}

data Free (K : hSpecies 2 ℓ₁ ℓ₂) : FinSet ℓ₁ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂)) where
  Op    : ∀ A → typ (K A) → Free K A
  unit  : Free K (⊤-FinSet ℓ₁)
  graft : ∀ A (B : ⟦ A ⟧ → FinSet ℓ₁) → Free K A →
            ((a : ⟦ A ⟧) → Free K (B a)) → Free K (Σⁿ A B)
  fidl   : ∀ A t →
             PathP (λ i → Free K (Σⁿ-Idl {A = A} i))
                   (graft (⊤-FinSet ℓ₁) (λ _ → A) unit λ _ → t) t
  fidr   : ∀ A t →
             PathP (λ i → Free K (Σⁿ-Idr {A = A} i))
                   (graft A (λ _ → ⊤-FinSet ℓ₁) t λ _ → unit) t
  fassoc : ∀ A B C t ts tss →
             PathP (λ i → Free K (Σⁿ-Assoc A B C i))
                   (graft (Σⁿ A B) (uncurry C) (graft A B t ts) (uncurry tss))
                   (graft A (λ a → Σⁿ (B a) (C a)) t λ a → graft (B a) (C a) (ts a) (tss a))
  set/  : ∀ A → isSet (Free K A)

open Operad

fassoc′ : (K : hSpecies 2 ℓ₁ ℓ₂) → ∀ n ns (nss : (i : Fin n) → Fin (ns i) → ℕ) t ts tss →
           let A     = n-FinSet n
               B     = n-FinSet ∘ ns ∘ lower
               C i j = n-FinSet (nss (lower i) (lower j))
            in PathP (λ i → Free K (Σⁿ-Assoc A B C i))
                     (graft (Σⁿ A B) (uncurry C) (graft A B t ts) (uncurry tss))
                     (graft A (λ a → Σⁿ (B a) (C a)) t λ a → graft (B a) (C a) (ts a) (tss a))
fassoc′ K n ns nss t ts tss =
  fassoc (n-FinSet n) (n-FinSet ∘ ns ∘ lower)
         (λ i j → n-FinSet (nss (lower i) (lower j)))
         t ts tss

FreeOperad : (K : hSpecies 2 ℓ₁ ℓ₂) → Operad ℓ₁ (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
K      (FreeOperad K) A = Free K A , set/ A
id     (FreeOperad K)   = unit
comp   (FreeOperad K)   = graft
idl′   (FreeOperad K) n k = transport (PathP≡Path _ _ _) (fidl (n-FinSet n) k)
idr′   (FreeOperad K) n k = transport (PathP≡Path _ _ _) (fidr (n-FinSet n) k)
assoc′ (FreeOperad K) n ns nss k ks kss = {!!}
  -- transport (PathP≡Path _ _ _)
  --          (fassoc (n-FinSet n) (n-FinSet ∘ ns ∘ lower)
  --                  (λ i j → n-FinSet (nss (lower i) (lower j)))
  --                  k ks kss)

η : (K′ : hSpecies 2 ℓ₁ ℓ₂) → K′ ⇒ˢˢ K (FreeOperad K′)
η K′ = Op

interpret : (K′ : hSpecies 2 ℓ₁ ℓ₂)
            (O : Operad ℓ₁ ℓ₂)
            (F : K′ ⇒ˢˢ K O) →
            ∀ A → Free K′ A → Ops O A
interpret K′ O F _ (Op _ x) = F _ x
interpret K′ O F _ unit = id O
interpret K′ O F _ (graft A B t ts) =
  comp O A B (interpret K′ O F _ t) λ a → interpret K′ O F _ (ts a)
interpret K′ O F _ (fidl A t i) =
  transport (sym (PathP≡Path (λ i → Ops O (Σⁿ-Idl {A = A} i)) _ _))
            (idl O A (interpret K′ O F A t)) i
interpret K′ O F _ (fidr A t i) =
  transport (sym (PathP≡Path (λ i → Ops O (Σⁿ-Idr {A = A} i)) _ _))
            (idr O A (interpret K′ O F A t)) i
interpret K′ O F _ (fassoc n ns nss t ts tss i) = {!!}
interpret K′ O F _ (set/ _ t t₁ x y i i₁) = {!!}

open _⇒ᵒᵖ_

ε : (O : Operad ℓ₁ ℓ₂) → FreeOperad (K O) ⇒ᵒᵖ O
⟪ ε O ⟫ = interpret (K O) O (idˢˢ (K O)) _
id-resp (ε O) = refl
∘-resp (ε O) A B a b = refl
