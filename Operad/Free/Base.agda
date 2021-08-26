{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Free.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (comp)

open import Cubical.Data.FinData
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels

open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma hiding (comp)
open import Cubical.Foundations.Transport

open import Operad.FinSet.Small
open import Operad.Base

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level

data Free (K : FinSetD ℓ₁ → Type ℓ₂) : FinSetD ℓ₁ → Type (ℓ-suc (ℓ-max ℓ₁ ℓ₂)) where
  Op    : ∀ A → K A → Free K A
  unit  : Free K ⊤F
  graft : ∀ A B → Free K A → (∀ a → Free K (B a)) → Free K (ΣF A B)
  fidl : ∀ A t → PathP (λ i → Free K (ΣIdL A i))
                       (graft ⊤F A unit t) (t (lift zero))
  fidr : ∀ A t → PathP (λ i → Free K (ΣIdR A i))
                       (graft A (λ _ → ⊤F) t λ _ → unit) t
  fassoc : ∀ A B C t ts tss →
             PathP (λ i → Free K (ΣAssoc A B C i))
                   (graft (ΣF A B) (uncurry C) (graft A B t ts) (uncurry tss))
                   (graft A (λ a → ΣF (B a) (C a)) t λ a → graft (B a) (C a) (ts a) (tss a))
  set/ : ∀ A → isSet (Free K A)

open Operad

FreeOperad : (K : FinSetD ℓ₁ → Type ℓ₂) →
             Operad ℓ₁ (ℓ-suc (ℓ-max ℓ₁ ℓ₂))
Ops      (FreeOperad K) = Free K
isSetOps (FreeOperad K) = set/
id       (FreeOperad K) = unit
comp     (FreeOperad K) = graft
idl      (FreeOperad K) = fidl
idr      (FreeOperad K) = fidr
assoc    (FreeOperad K) = fassoc
