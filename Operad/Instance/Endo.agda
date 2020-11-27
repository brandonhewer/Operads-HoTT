{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Instance.Endo where

open import Cubical.Data.FinData
open import Cubical.Data.Nat

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Structure

open import Operad.Base
open import Operad.FinSet

private
  variable
    ℓ₁ ℓ₂ : Level

open Operad

Endo : hSet ℓ₁ → Operad ℓ₁ ℓ₁
K (Endo (X , isSetX)) A = ((⟦ A ⟧ → X) → X) , isSetΠ λ _ → isSetX
id (Endo (X , isSetX)) x = x (lift zero)
comp (Endo (X , isSetX)) A B f gs h = f λ a → gs a λ b → h (a , b)
idl′ (Endo {ℓ₁} (X , isSetX)) n f = funExt λ xs →
  transp (λ i → X) i0 _                           ≡⟨ transportRefl _ ⟩
  f (λ b → transp (λ i → X) i0 _)                 ≡⟨ cong f (funExt λ _ → transportRefl _) ⟩
  f (λ b → xs (transp (λ i → Lift (Fin n)) i0 _)) ≡⟨ cong f (funExt λ _ → cong xs (transportRefl _)) ⟩
  f xs                                            ∎
idr′ (Endo (X , isSetX)) = {!!}
assoc′ (Endo (X , isSetX)) n ns nss k ks kss = {!!}
