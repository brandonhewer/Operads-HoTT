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

open Operad

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

open import Cubical.Foundations.Equiv

{-
cong₃ : {ℓ : Level} {A : Type ℓ} {B : A → Type ℓ}
        {C : (a : A) (b : B a) → Type ℓ}
        {D : (a : A) (b : B a) → C a b → Type ℓ} →
        (f : (a : A) (b : B a) (c : C a b) → D a b c) →
        {x y : A}
        (p : x ≡ y) →
        {u : B x} {v : B y} (q : PathP (λ i → B (p i)) u v) →
        {s : C x u} {t : C y v} (r : PathP (λ i → C (p i) (q i)) s t) →
        PathP (λ i → D (p i) (q i) (r i)) (f x u s) (f y v t)
cong₃ f p q r i = f (p i) (q i) (r i)

Endo⁻ : {X : Type ℓ₁} → isSet X → Operad ℓ₁ ℓ₁
Ops (Endo⁻ {X = X} isSetX) A = El A → X → X
isSetOps (Endo⁻ isSetX) _ = isSetΠ (const (isSetΠ (const isSetX)))
id (Endo⁻ isSetX) _ x = x
comp (Endo⁻ isSetX) A B f fs (a , b) x = f a (fs a b x)
idl (Endo⁻ {X = X} isSetX) A f =
  transport⁻ (PathP≡Path _ _ _) (funExt λ xs → funExt λ ys →
     transp (λ i → X) i0 _ ≡⟨ transportRefl _ ⟩
     f _ _                 ≡⟨ cong₂ f (transportRefl _) (transportRefl _) ⟩
     f xs ys               ∎
  )
idr (Endo⁻ {X = X} isSetX) A f =
  transport⁻ (PathP≡Path _ _ _) (funExt λ xs → funExt λ ys →
     transp (λ i → X) i0 _ ≡⟨ transportRefl _ ⟩
     f _ _                 ≡⟨ cong₂ f (transportRefl _) (transportRefl _) ⟩
     f xs ys               ∎
  )
assoc (Endo⁻ {X = X} isSetX) A B C f fs fss =
  transport⁻ (PathP≡Path _ _ _) (funExt λ a → funExt λ x →
    transp (λ i → X) i0 _ ≡⟨ transportRefl _ ⟩
    f _ (fs _ _ (fss _ _ _ (transp (λ i → X) i0 x))) ≡⟨
      cong (f _) (cong (fs _ _) (cong (fss _ _ _) (transportRefl _)))
    ⟩
    f (transp (λ i → El A) i0 _) _ ≡⟨
      cong₂ f (transportRefl (fst a)) refl
    ⟩
    f _ (fs (transp (λ i → El A) i0 (fst a)) _ _) ≡⟨
      {!!}
    ⟩
    {!!}
  )
-}
{-
f (fst a)
(fs (transp (λ i → El A) i0 (fst a))
 (transp (λ i → El (B (transp (λ i₁ → El A) (~ i) (fst a)))) i0
  (fst (snd a)))
 (fss (transp (λ i → El A) i0 (fst a))
  (transp (λ i → El (B (transp (λ i₁ → El A) (~ i) (fst a)))) i0
   (fst (snd a)))
  (transp
   (λ i →
      El
      (C (transp (λ i₁ → El A) (~ i) (fst a))
       (transp (λ i₁ → El (B (transp (λ i₂ → El A) (~ i₁ ∨ ~ i) (fst a))))
        (~ i) (fst (snd a)))))
   i0 (snd (snd a)))
  x))
-}
