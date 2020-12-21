{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Instance.Endo where

open import Cubical.Data.Nat

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Operad.Base
open import Operad.Fin
open import Operad.FinSet.Small
open import Operad.Sigma hiding (comp)

private
  variable
    ℓ₁ ℓ₂ : Level

open Operad

open import Cubical.Foundations.Equiv

Endo : {X : Type ℓ₁} → isSet X → Operad ℓ₁ ℓ₁
Ops (Endo {X = X} isSetX) A = (El A → X) → X
isSetOps (Endo isSetX) A = isSetΠ λ _ → isSetX
id (Endo isSetX) f = f (lift zero)
comp (Endo isSetX) A B f gs h = f λ a → gs a λ b → h (a , b)
idl (Endo {X = X} isSetX) A f =
  transport⁻ (PathP≡Path _ _ _) (funExt λ xs →
    transp (λ i → X) i0 _                   ≡⟨ transportRefl _ ⟩
    f (λ _ → transp (λ i → X) i0 _)         ≡⟨ cong f (funExt λ _ → transportRefl _) ⟩
    f (λ _ → xs (transp (λ i → El A) i0 _)) ≡⟨ cong f (funExt λ _ → cong xs (transportRefl _)) ⟩
    f (λ _ → xs (transp (λ i → El A) i0 _)) ≡⟨ cong f (funExt λ _ → cong xs (transportRefl _)) ⟩
    f xs                                    ∎
  )
idr (Endo {X = X} isSetX) A f =
  transport⁻ (PathP≡Path _ _ _) (funExt λ xs →
    transp (λ i → X) i0 _                   ≡⟨ transportRefl _ ⟩
    f (λ _ → transp (λ i → X) i0 _)         ≡⟨ cong f (funExt λ _ → transportRefl _) ⟩
    f (λ _ → xs (transp (λ i → El A) i0 _)) ≡⟨ cong f (funExt λ _ → cong xs (transportRefl _)) ⟩
    f xs                                    ∎
  )
assoc (Endo {X = X} isSetX) A B C f fs fss =
  transport⁻ (PathP≡Path _ _ _) (funExt λ xs →
    transp (λ i → X) i0 _
      ≡⟨ transportRefl _ ⟩
    f (λ _ → fs _ λ _ → fss _ _ λ _ → transp (λ i → X) i0 _)
      ≡⟨ cong f (funExt λ _ →
                  cong (fs _) (funExt λ _ →
                    cong (fss _ _) (funExt λ _ →
                      transportRefl _))) ⟩
    f (λ _ → fs _ λ _ → fss _ _ λ _ →
         xs (transp (λ i → Σ (El A) λ a → Σ (El (B a)) (El ∘ C a)) i0 _))
      ≡⟨ cong f (funExt λ _ →
                  cong (fs _) (funExt λ _ →
                    cong (fss _ _) (funExt λ _ →
                      cong xs (transportRefl _)))) ⟩
    f _ ∎
  )
