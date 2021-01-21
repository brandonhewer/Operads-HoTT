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
open import Operad.Morphism
open import Operad.Fin
open import Operad.FinSet.Small
open import Operad.Sigma hiding (comp)

private
  variable
    ℓ₁ ℓ₂ : Level

  open Iso

  endo-transp≡ : {A₁ A₂ :  Type ℓ₁} {B : Type ℓ₂} (p : Iso A₁ A₂)
                 (f : (A₂ → B) → B) →
                 subst (λ A → (A → B) → B) (isoToPath p)
                       (λ h → f (h ∘ inv p)) ≡ f
  endo-transp≡ {A₂ = A₂} {B = B} p f = funExt λ xs →
    transp (λ i → B) i0 _                   ≡⟨ transportRefl _ ⟩
    f (λ _ → transp (λ i → B) i0 _)         ≡⟨ cong f (funExt λ _ → transportRefl _) ⟩
    f (λ _ → xs (transp (λ i → A₂) i0 _))   ≡⟨ cong f (funExt λ _ → cong xs (transportRefl _)) ⟩
    _                                       ≡⟨ cong f (funExt λ _ → cong xs (rightInv p _)) ⟩
    f xs                                    ∎

  endo-≡ : {A₁ A₂ :  Type ℓ₁} {B : Type ℓ₂} (p : Iso A₁ A₂)
           (f : (A₂ → B) → B) →
           PathP (λ i → (isoToPath p i → B) → B)
                 (λ h → f (λ a → h (inv p a))) f
  endo-≡ p = transport⁻ (PathP≡Path _ _ _) ∘ endo-transp≡ p

  endo⁻-transp≡ : {A₁ A₂ :  Type ℓ₁} {B : Type ℓ₂} (p : Iso A₁ A₂)
                  (f : A₁ → B → B) →
                  subst (λ A → A → B → B) (isoToPath p)
                        f ≡ (f ∘ inv p)
  endo⁻-transp≡ {A₁ = A₁} {A₂ = A₂} {B = B} p f = funExt λ xs → funExt λ ys →
    transp (λ i → B) i0 _ ≡⟨ transportRefl _ ⟩
    _                     ≡⟨ cong₂ f (cong (inv p) (transportRefl _)) (transportRefl _) ⟩
    _                     ∎

  endo⁻-≡ : {A₁ A₂ :  Type ℓ₁} {B : Type ℓ₂} (p : Iso A₁ A₂)
             (f : A₁ → B → B) →
             PathP (λ i → isoToPath p i → B → B)
                   f (f ∘ inv p)
  endo⁻-≡ p = transport⁻ (PathP≡Path _ _ _) ∘ endo⁻-transp≡ p              

open Operad

Endo : {X : Type ℓ₁} → isSet X → Operad ℓ₁ ℓ₁
Ops (Endo {X = X} isSetX) A = (El A → X) → X
isSetOps (Endo isSetX) A = isSetΠ λ _ → isSetX
id (Endo isSetX) f = f (lift zero)
comp (Endo isSetX) A B f gs h = f λ a → gs a λ b → h (a , b)
idl (Endo {X = X} isSetX) A = endo-≡ Σ-Idl
idr (Endo {X = X} isSetX) A = endo-≡ Σ-Idr
assoc (Endo {X = X} isSetX) A B C f fs fss = endo-≡ Σ-assoc-Iso _

Endo⁻ : {X : Type ℓ₁} → isSet X → Operad ℓ₁ ℓ₁
Ops (Endo⁻ {X = X} isSetX) A = El A → X → X
isSetOps (Endo⁻ isSetX) _ = isSetΠ (const (isSetΠ (const isSetX)))
id (Endo⁻ isSetX) _ x = x
comp (Endo⁻ isSetX) A B f fs (a , b) x = f a (fs a b x)
idl (Endo⁻ isSetX) A f = endo⁻-≡ Σ-Idl (f ∘ snd)
idr (Endo⁻ isSetX) A f = endo⁻-≡ Σ-Idr (f ∘ fst)
assoc (Endo⁻ isSetX) A B C f fs fss = endo⁻-≡ Σ-assoc-Iso _
