{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Species.Properties where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.Relation.Nullary

open import Operad.FinSet.Base
open import Operad.Species.Base
open import Operad.Species.Morphism
open import Operad.Sum

private
  variable
    i j : HLevel
    ℓ₁ ℓ₂ ℓ₃ : Level

toSpecies : (K : FinSet ℓ₁ → Type ℓ₂) (P : ∀ A → K A → Type ℓ₃) →
            (∀ A k → isProp (P A k)) → Species 1 ℓ₁ _
toSpecies K P isPropP A = ((k : K A) → P A k) , isPropΠ λ _ → isPropP _ _

hFree* : ∀ n → Species (suc (suc i)) ℓ₁ ℓ₂ → *Species (suc (suc i)) ℓ₁ ℓ₂ n
hFree* n K X with discreteℕ n (card X)
hFree* {i} n K X | yes p =
  ((typ (K X) ⊎ ⊤) ,
   isOfHLevelSum _ (str (K X)) (isProp→isOfHLevelSuc (suc i) isPropUnit)) ,
  λ p → inr _
hFree* n K X | no ¬p = K X , ⊥-rec ∘ ¬p

Free* : ∀ n → (FinSet ℓ₁ → Type ℓ₂) → *Species′ ℓ₁ ℓ₂ n
Free* n K X with discreteℕ n (card X)
Free* n K X | yes p = K X ⊎ ⊤ , λ p → inr _
Free* n K X | no ¬p = K X , ⊥-rec ∘ ¬p

hFree*[_∣_] : ∀ n {K₁ : Species (suc (suc i)) ℓ₁ ℓ₂} {K₂ : Species (suc (suc j)) ℓ₁ ℓ₃} →
              _⇒ˢ_ {i = suc (suc i)} {j = suc (suc j)} K₁ K₂ →
              _⇒*_ {i = suc (suc i)} {j = suc (suc j)} (hFree* n K₁) (hFree* n K₂)
hFree*[ n ∣ f ] X with discreteℕ n (card X)
hFree*[ n ∣ f ] X | yes p = [ inl ∘ f X , inr ] , λ _ → ∣ refl ∣
hFree*[ n ∣ f ] X | no ¬p = f X , ⊥-rec ∘ ¬p

Free*[_∣_] : ∀ n {K₁ : FinSet ℓ₁ → Type ℓ₂} {K₂ : FinSet ℓ₁ → Type ℓ₃} →
              (∀ X → K₁ X → K₂ X) →
              (Free* n K₁) ⇒*′ (Free* n K₂)
Free*[ n ∣ f ] X with discreteℕ n (card X)
Free*[ n ∣ f ] X | yes p = [ inl ∘ f X , inr ] , λ _ → ∣ refl ∣
Free*[ n ∣ f ] X | no ¬p = f X , ⊥-rec ∘ ¬p

hη* : ∀ n (K : Species (suc (suc i)) ℓ₁ ℓ₂) →
        _⇒ˢ_ {i = suc (suc i)} {j = suc (suc i)} K (fst ∘ hFree* n K)
hη* n K X k with discreteℕ n (card X)
hη* n K X k | yes p = inl k
hη* n K X k | no ¬p = k

η* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) → ∀ X → K X → fst (Free* n K X)
η* n K X k with discreteℕ n (card X)
η* n K X k | yes p = inl k
η* n K X k | no ¬p = k

left* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) (*K : *Species′ ℓ₁ ℓ₃ n)
            (f : ∀ X → K X → fst (*K X)) → Free* n K ⇒*′ *K
left* n K *K f X with discreteℕ n (card X)
left* n K *K f X | yes p =
  [ f X , const (snd (*K X) p) ] , λ q → ? --  ∣ cong (snd (*K X)) (isSetℕ _ _ _ _) ∣
left* n K *K f X | no ¬p = f X , ⊥-rec ∘ ¬p

left*P : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) (*K : *Species′ ℓ₁ ℓ₃ n)
             (f : ∀ X → K X → fst (*K X)) →
         ∀ X k → fst (left* n K *K f X) (η* n _ _ k) ≡ f X k
left*P n K *K f X k with discreteℕ n (card X)
left*P n K *K f X k | yes p = refl
left*P n K *K f X k | no ¬p = refl

unique* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) (*K : *Species′ ℓ₁ ℓ₃ n)
            (f : ∀ X → K X → fst (*K X)) →
            (g : Free* n K ⇒*′ *K) →
            (p : ∀ X k → fst (g X) (η* n _ _ k) ≡ f X k) →
            ∀ X → left* n K *K f X ≡ g X
unique* n K *K f g p X = {!!}

hε* : ∀ n (K : *Species (suc (suc i)) ℓ₁ ℓ₂ n) →
        _⇒*_ {i = suc (suc i)} {j = suc (suc i)} (hFree* n (fst ∘ K)) K
hε* n K X with discreteℕ n (card X)
hε* n K X | yes p = [ (λ k → k) , const (snd (K X) p) ] ,
                    λ q → ∣ cong (snd (K X)) (isSetℕ _ _ _ _) ∣
hε* n K X | no ¬p = (λ k → k) , ⊥-rec ∘ ¬p

ε* : ∀ n (K : *Species′ ℓ₁ ℓ₂ n) → (Free* n (fst ∘ K)) ⇒*′ K
ε* n K X with discreteℕ n (card X)
ε* n K X | yes p = [ (λ k → k) , const (snd (K X) p) ] ,
                    λ q → ∣ cong (snd (K X)) (isSetℕ _ _ _ _) ∣
ε* n K X | no ¬p = (λ k → k) , ⊥-rec ∘ ¬p

hzig* : ∀ n (K : *Species (suc (suc i)) ℓ₁ ℓ₂ n) →
        ∀ X k → fst (hε* n K X) (hη* n (fst ∘ K) X k) ≡ k
hzig* n K X k with discreteℕ n (card X)
hzig* n K X k | yes p = refl
hzig* n K X k | no ¬p = refl

zig* : ∀ n (K : *Species′ ℓ₁ ℓ₂ n) →
       ∀ X k → fst (ε* n K X) (η* n (fst ∘ K) X k) ≡ k
zig* n K X k with discreteℕ n (card X)
zig* n K X k | yes p = refl
zig* n K X k | no ¬p = refl
