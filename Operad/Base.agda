{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude hiding (comp)

open import Operad.Fin
open import Operad.FinSet.Small
open import Operad.FinSet.Small.Properties

private
  variable
    ℓ₁ ℓ₂ : Level

record Operad (ℓ₁ ℓ₂ : Level) : Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂)) where
  field
    Ops      : FinSetD ℓ₁ → Type ℓ₂
    isSetOps : ∀ A → isSet (Ops A) 
    id       : Ops ⊤F
    comp     : ∀ A B → Ops A → (∀ a → Ops (B a)) → Ops (ΣF A B)

    idl      : ∀ A k → PathP (λ i → Ops (ΣIdL A i))
                             (comp ⊤F (const A) id (const k)) k
    idr      : ∀ A k → PathP (λ i → Ops (ΣIdR A i))
                             (comp A (const ⊤F) k (const id)) k
    assoc    : ∀ A B C k ks kss →
                 PathP (λ i → Ops (ΣAssoc A B C i))
                       (comp (ΣF A B) (uncurry C) (comp A B k ks) (uncurry kss))
                       (comp A (λ a → ΣF (B a) (C a)) k
                             λ a → comp (B a) (C a) (ks a) (kss a))
