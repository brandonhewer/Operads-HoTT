{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Ordered.Base where

open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)

open import Operad.Base
open import Operad.Fin
open import Operad.FinSet.Small

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level

  open Iso

  Lift-inj : {A B : Type ℓ₁} →
             Iso (Lift {j = ℓ₂} A) (Lift {j = ℓ₃} B) → Iso A B
  fun      (Lift-inj I) = lower ∘ fun I ∘ lift
  inv      (Lift-inj I) = lower ∘ inv I ∘ lift
  rightInv (Lift-inj I) = cong lower ∘ rightInv I ∘ lift
  leftInv  (Lift-inj I) = cong lower ∘ leftInv I ∘ lift

  FinL : ℕ → FinSetD ℓ₁
  FinL n = Ty (Lift (Fin n) , n , ∣ invIso LiftIso ∣)

  FinL-inj : ∀ {m n} → FinL {ℓ₁} m ≡ FinL n → m ≡ n
  FinL-inj = Fin-inj ∘ Lift-inj ∘ equivToIso ∘ pathToEquiv ∘ cong El

  FinL-inj-tr : ∀ {m n} → ∥ FinL {ℓ₁} m ≡ FinL n ∥ → m ≡ n
  FinL-inj-tr p = prec (isSetℕ _ _) FinL-inj p

FinRestrict : (K : FinSetD ℓ₁ → Type ℓ₂) → ℕ → Type ℓ₂
FinRestrict K n = K (FinL n)

FinExtend : (K : ℕ → Type ℓ₂) → FinSetD ℓ₁ → Type _
FinExtend K A = Σ[ n ∈ ℕ ] K n × ∥ FinL n ≡ A ∥

FinExtend≡ : (K : ℕ → Type ℓ₂) (A : FinSetD ℓ₁)
             (x y : FinExtend K A) →
             (p : fst x ≡ fst y) →
             PathP (λ i → K (p i)) (fst (snd x)) (fst (snd y)) →
             x ≡ y
FinExtend≡ K A x y p q i =
  p i , q i ,
  isProp→PathP (λ i → squash {A = FinL (p i) ≡ A}) (snd (snd x)) (snd (snd y)) i  

extendRestrict : (K : ℕ → Type (ℓ-max (ℓ-suc ℓ₁) ℓ₂)) →
                 ∀ n → Iso (FinRestrict {ℓ₁} (FinExtend K) n) (K n)
fun (extendRestrict K n) (m , k , p) = subst K (FinL-inj-tr p) k
inv (extendRestrict K n) k = n , k , ∣ refl ∣
rightInv (extendRestrict K n) k =
  cong (λ p → subst K p k) (isSetℕ _ _ _ refl) ∙ substRefl {B = K} k
leftInv (extendRestrict K n) (m , k , p) =
  FinExtend≡ _ _ _ _ (sym (FinL-inj-tr p))
                     (symP {A = λ i → K (FinL-inj-tr p i)}
                           (subst-filler K (FinL-inj-tr p) k))

FinERIso : Iso (FinSetD ℓ₁ → Type _) (ℕ → Type (ℓ-max (ℓ-suc ℓ₁) ℓ₂))
fun FinERIso K = FinRestrict K
inv FinERIso K = FinExtend K
rightInv (FinERIso {ℓ₂ = ℓ₂}) K = funExt (isoToPath ∘ extendRestrict {ℓ₂ = ℓ₂} K)
leftInv FinERIso K = funExt λ A → {!!}
