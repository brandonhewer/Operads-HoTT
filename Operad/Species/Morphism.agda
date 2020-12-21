{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Species.Morphism where

open import Cubical.Data.Nat

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Operad.FinSet
open import Operad.Species.Base

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    n : ℕ
    i j k : HLevel

_⇒ˢ_ : Species i ℓ₁ ℓ₂ → Species j ℓ₁ ℓ₃ → Type _
K₁ ⇒ˢ K₂ = ∀ X → typ (K₁ X) → typ (K₂ X)

_⇒ˢˢ_ : Species 2 ℓ₁ ℓ₂ → Species 2 ℓ₁ ℓ₃ → Type _
_⇒ˢˢ_ = _⇒ˢ_ {i = 2} {j = 2}

_∘ˢ_ : {K₁ : Species i ℓ₁ ℓ₂} {K₂ : Species j ℓ₁ ℓ₃} {K₃ : Species k ℓ₁ ℓ₄} →
       K₂ ⇒ˢ K₃ → K₁ ⇒ˢ K₂ → K₁ ⇒ˢ K₃
(f ∘ˢ g) X = f X ∘ g X

_∘ˢˢ_ : {K₁ : Species 2 ℓ₁ ℓ₂} {K₂ : Species 2 ℓ₁ ℓ₃} {K₃ : Species 2 ℓ₁ ℓ₄} →
       K₂ ⇒ˢˢ K₃ → K₁ ⇒ˢˢ K₂ → K₁ ⇒ˢˢ K₃
(f ∘ˢˢ g) X = f X ∘ g X

_⇒*_ : *Species i ℓ₁ ℓ₂ n → *Species j ℓ₁ ℓ₃ n → Type _
_⇒*_ {ℓ₁ = ℓ₁} {n = n} K₁ K₂ =
  (X : FinSet ℓ₁) →
  Σ[ f ∈ (typ (fst (K₁ X)) → typ (fst (K₂ X))) ]
    ((p : n ≡ card X) → ∥ f (snd (K₁ X) p) ≡ snd (K₂ X) p ∥)

⇒*′-res : (X : FinSet ℓ₁) → PointedSpecies′ ℓ₂ n X → PointedSpecies′ ℓ₃ n X → Type _
⇒*′-res {n = n} X K₁ K₂ =
  Σ[ f ∈ (fst K₁ → fst K₂) ]
  ((p : n ≡ card X) → ∥ f (snd K₁ p) ≡ snd K₂ p ∥)

_⇒*′_ : *Species′ ℓ₁ ℓ₂ n → *Species′ ℓ₁ ℓ₃ n → Type _
_⇒*′_ {ℓ₁ = ℓ₁} {n = n} K₁ K₂ =
  (X : FinSet ℓ₁) → ⇒*′-res X (K₁ X) (K₂ X)

_∘*_ : {K₁ : *Species i ℓ₁ ℓ₂ n} {K₂ : *Species j ℓ₁ ℓ₃ n} {K₃ : *Species k ℓ₁ ℓ₄ n} →
       K₂ ⇒* K₃ → K₁ ⇒* K₂ → K₁ ⇒* K₃
(g ∘* f) X =
  fst (g X) ∘ fst (f X) , λ p →
    p-rec propTruncIsProp (λ pf →
      p-rec propTruncIsProp (λ pg →
        ∣ cong (fst (g X)) pf ∙ pg ∣
      ) (snd (g X) p)
    ) (snd (f X) p)

_∘*′_ : {K₁ : *Species′ ℓ₁ ℓ₂ n} {K₂ : *Species′ ℓ₁ ℓ₃ n} {K₃ : *Species′ ℓ₁ ℓ₄ n} →
        K₂ ⇒*′ K₃ → K₁ ⇒*′ K₂ → K₁ ⇒*′ K₃
(g ∘*′ f) X =
  fst (g X) ∘ fst (f X) , λ p →
    p-rec propTruncIsProp (λ pf →
      p-rec propTruncIsProp (λ pg →
        ∣ cong (fst (g X)) pf ∙ pg ∣
      ) (snd (g X) p)
    ) (snd (f X) p)

idˢ : (K : Species i ℓ₁ ℓ₂) → K ⇒ˢ K
idˢ K X k = k

idˢˢ : (K : Species 2 ℓ₁ ℓ₂) → K ⇒ˢˢ K
idˢˢ K X k = k

id* : (K : *Species i ℓ₁ ℓ₂ n) → K ⇒* K
id* K X = (λ k → k) , λ _ → ∣ refl ∣

id*′ : (K : *Species′ ℓ₁ ℓ₂ n) → K ⇒*′ K
id*′ K X = (λ k → k) , λ _ → ∣ refl ∣

_≡*_ : {K₁ K₂ : *Species i ℓ₁ ℓ₂ n} → K₁ ⇒* K₂ → K₁ ⇒* K₂ → Type _
f ≡* g = ∀ X k → fst (f X) k ≡ fst (g X) k

_≡*′_ : {K₁ : *Species′ ℓ₁ ℓ₂ n} {K₂ : *Species′ ℓ₁ ℓ₃ n} →
        K₁ ⇒*′ K₂ → K₁ ⇒*′ K₂ → Type _
f ≡*′ g = ∀ X k → fst (f X) k ≡ fst (g X) k
