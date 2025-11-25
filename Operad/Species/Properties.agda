{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Species.Properties where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Sum
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Cubical.Relation.Nullary

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.Species.Base
open import Operad.Species.Combinators
open import Operad.Species.Morphism
open import Operad.Sum

private
  variable
    n : ℕ
    i j : HLevel
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level

  isProp→isOfHLevel⊔1 : ∀ {A : Type ℓ₁} n → isProp A → isOfHLevel (n ⊔ 1) A
  isProp→isOfHLevel⊔1 zero p = p
  isProp→isOfHLevel⊔1 {A = A} (suc n) p =
    subst (λ m → isOfHLevel (suc m) A) (sym (⊔-idr n))
          (isProp→isOfHLevelSuc n p) 

toSpecies : (K : FinSet ℓ₁ → Type ℓ₂) (P : ∀ A → K A → Type ℓ₃) →
            (∀ A k → isProp (P A k)) → Species 1 ℓ₁ _
toSpecies K P isPropP A = ((k : K A) → P A k) , isPropΠ λ _ → isPropP _ _

isOfHLevel⇒* : (K₁ : *Species i ℓ₁ ℓ₂ n) (K₂ : *Species j ℓ₁ ℓ₃ n) →
               isOfHLevel (j ⊔ 1) (K₁ ⇒* K₂)
isOfHLevel⇒* K₁ K₂ = isOfHLevelΠ _ λ A →
                     isOfHLevelΣ _ (
                     isOfHLevelΠ _ λ _ → isOfHLevel⊔ _ (str (fst (K₂ A))))
                     λ _ → isProp→isOfHLevel⊔1 _ (isPropΠ λ _ → propTruncIsProp)      

≡*′→≡ : {K₁ : *Species′ ℓ₁ ℓ₂ n} {K₂ : *Species′ ℓ₁ ℓ₃ n}
        (f : K₁ ⇒*′ K₂) (g : K₁ ⇒*′ K₂) → f ≡*′ g → f ≡ g
≡*′→≡ f g f≡*g =
  funExt λ X → Σ≡Prop (λ _ → isPropΠ λ _ → propTruncIsProp)
                      (funExt λ k → f≡*g X k)

Free* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) → *Species′ ℓ₁ ℓ₂ n
Free* n K X = (K X ⊎ (n ≡ card X)) , inr

Free*[_∣_] : ∀ n {K₁ : FinSet ℓ₁ → Type ℓ₂} {K₂ : FinSet ℓ₁ → Type ℓ₃} →
              (∀ X → K₁ X → K₂ X) →
              (Free* n K₁) ⇒*′ (Free* n K₂)
Free*[ n ∣ f ] X = [ inl ∘ f X , inr ] , λ _ → ∣ refl ∣

ε* : ∀ n (K : *Species′ ℓ₁ ℓ₂ n) → Free* n (fst ∘ K) ⇒*′ K
ε* n K X = [ (λ x → x) , snd (K X) ] , λ _ → ∣ refl ∣

zig* : ∀ n (K : *Species′ ℓ₁ ℓ₂ n) →
       ∀ X k → fst (ε* n K X) (inl k) ≡ k
zig* n K X k = refl

zag* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) →
         (ε* n (Free* n K) ∘*′ Free*[ n ∣ (λ _ → inl) ]) ≡*′ id*′ (Free* n K)
zag* n K X (inl x) = refl
zag* n K X (inr x) = refl

left* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) (*K : *Species′ ℓ₁ ℓ₃ n)
            (f : ∀ X → K X → fst (*K X)) → Free* n K ⇒*′ *K
left* n K *K f X = [ f X , snd (*K X) ] , λ _ → ∣ refl ∣

leftP* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) (*K : *Species′ ℓ₁ ℓ₃ n) →
             (f : ∀ X → K X → fst (*K X)) →
             ∀ X k → fst (left* n K *K f X) (inl k) ≡ f X k
leftP* n K *K f X k = refl

unique* : ∀ n (K : FinSet ℓ₁ → Type ℓ₂) (*K : *Species′ ℓ₁ ℓ₃ n) →
            (∀ X → isSet (fst (*K X))) →
            (f : ∀ X → K X → fst (*K X)) →
            (g : Free* n K ⇒*′ *K) →
            (p : ∀ X k → fst (g X) (inl k) ≡ f X k) →
            left* n K *K f ≡*′ g
unique* n K *K isSet*K f g p X (inl k) = sym (p X k)
unique* n K *K isSet*K f g p X (inr q) =
  p-rec (isSet*K _ _ _) sym (snd (g X) q)
