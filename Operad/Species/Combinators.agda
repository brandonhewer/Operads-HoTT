{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Species.Combinators where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Structure
open import Cubical.Foundations.Univalence

open import Cubical.HITs.SetTruncation renaming (rec to s-rec; elim to s-elim)

open import Cubical.Relation.Nullary

open import Operad.Fin
open import Operad.FinSet
open import Operad.Species.Base
open import Operad.Species.Morphism

data PartitionBy {ℓ₁ ℓ₂ : Level} {U : Type ℓ₁}
                 (E : U → Type ℓ₂) (Σ : ∀ u → (E u → U) → U)
                 : U → Type (ℓ-max ℓ₁ ℓ₂) where
  partition : (A : U) (B : E A → U) → PartitionBy E Σ (Σ A B)

Partition : {ℓ : Level} → FinSet ℓ → Type (ℓ-suc ℓ)
Partition = PartitionBy ⟦_⟧ Σⁿ

_⊔_ : ℕ → ℕ → ℕ
zero  ⊔ n     = n
suc m ⊔ zero  = suc m
suc m ⊔ suc n = suc (m ⊔ n)

⊔-idr : ∀ m → m ⊔ 0 ≡ m
⊔-idr zero    = refl
⊔-idr (suc m) = refl

⊔-comm : ∀ m n → m ⊔ n ≡ n ⊔ m
⊔-comm zero    zero    = refl
⊔-comm zero    (suc n) = refl
⊔-comm (suc m) zero    = refl
⊔-comm (suc m) (suc n) = cong suc (⊔-comm m n)

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level
    i j k l : HLevel
    X : FinSet ℓ₁

  PartitionBy′ : {U : Type ℓ₁}
                 (E : U → Type ℓ₂)
                 (Σ : ∀ u → (E u → U) → U) →
                 U → Type (ℓ-max ℓ₁ ℓ₂)
  PartitionBy′ {U = U} E Σ X = Σ[ A ∈ U ] Σ[ B ∈ (E A → U) ] Σ A B ≡ X

  Partition′ : FinSet ℓ₁ → Type (ℓ-suc ℓ₁)
  Partition′ {ℓ₁} X = Σ[ A ∈ FinSet ℓ₁ ] Σ[ B ∈ (⟦ A ⟧ → FinSet ℓ₁) ] Σⁿ A B ≡ X

  Partition′→Partition : Partition′ X → Partition X
  Partition′→Partition (A , B , p) = subst Partition p (partition A B)

  Partition→Partition′ : Partition X → Partition′ X
  Partition→Partition′ (partition A B) = A , B , refl

  PartitionRetract : ∀ P → Partition′→Partition {X = X} (Partition→Partition′ P) ≡ P
  PartitionRetract (partition A B) = substRefl {B = Partition} (partition A B)

  isGroupoidPartition′ : isGroupoid (Partition′ X)
  isGroupoidPartition′ {X = X} = isGroupoidΣ isGroupoidFinSet λ A →
                                             isGroupoidΣ (isGroupoidΠ λ _ → isGroupoidFinSet)
                                                         λ _ → isSet→isGroupoid (isGroupoidFinSet _ _)

isOfHLevel⊔ : ∀ {m} {ℓ₁} {A : Type ℓ₁} n → isOfHLevel m A → isOfHLevel (m ⊔ n) A
isOfHLevel⊔ {0}                                 = isContr→isOfHLevel
isOfHLevel⊔ {suc m}       0             p     = p
isOfHLevel⊔ {1}           (suc n)             = isProp→isOfHLevelSuc n
isOfHLevel⊔ {suc (suc m)} 1             p     = p
isOfHLevel⊔ {suc (suc m)} (suc (suc n)) p x y = isOfHLevel⊔ {suc m} (suc n) (p x y)

isOfHLevelΣ′ : {A : Type ℓ₁} {B : A → Type ℓ₂} →
               ∀ m n → isOfHLevel m A → ((x : A) → isOfHLevel n (B x))
                     → isOfHLevel (m ⊔ n) (Σ A B)
isOfHLevelΣ′ m n h₁ h₂ = isOfHLevelΣ _ (isOfHLevel⊔ _ h₁)
                            (subst (flip isOfHLevel _) (⊔-comm n m) ∘
                             isOfHLevel⊔ m ∘ h₂)

index : {X : FinSet ℓ₁} → Partition X → FinSet ℓ₁
index (partition A _) = A

elem : {X : FinSet ℓ₁} (P : Partition X) (a : ⟦ index P ⟧) → FinSet ℓ₁
elem (partition _ B) a = B a

isGroupoidPartition : isGroupoid (Partition X)
isGroupoidPartition = isOfHLevelRetract 3 Partition→Partition′
                                          Partition′→Partition
                                          PartitionRetract
                                          isGroupoidPartition′

Partitioned : {X : FinSet ℓ₁} → Species i ℓ₁ ℓ₂ → Species j ℓ₁ ℓ₃ → Partition X → TypeOfHLevel _ (i ⊔ j)
Partitioned {i = i} {j = j} K₁ K₂ (partition A B) =
  typ (K₁ A) × ((a : ⟦ A ⟧) → typ (K₂ (B a))) ,
  isOfHLevelΣ′ i j (str (K₁ A)) λ _ → isOfHLevelΠ j λ a → str (K₂ (B a))

_⊚_ : Species i ℓ₁ ℓ₂ → Species j ℓ₁ ℓ₃ → Species (3 ⊔ (i ⊔ j)) _ _
_⊚_ {i = i} {j = j} K₁ K₂ X = (Σ (Partition X) (typ ∘ Partitioned K₁ K₂)) ,
                               isOfHLevelΣ′ 3 (i ⊔ j) isGroupoidPartition λ P → str (Partitioned K₁ K₂ P)

_⊚₂_ : Species 2 ℓ₁ ℓ₂ → Species 2 ℓ₁ ℓ₃ → Species 3 _ _
(K₁ ⊚₂ K₂) X = (_⊚_ {i = 2} {j = 2} K₁ K₂) X

_⟦⊚⟧_ : {K₁ : Species i ℓ₁ ℓ₂} {K₂ : Species j ℓ₁ ℓ₃}
        {K₃ : Species k ℓ₁ ℓ₄} {K₄ : Species l ℓ₁ ℓ₅} →
        (K₁ ⇒ˢ K₂) → (K₂ ⇒ˢ K₄) → (K₁ ⊚ K₂) ⇒ˢ (K₂ ⊚ K₄)
(f ⟦⊚⟧ g) .(Σⁿ A B) (partition A B , k , ks) = partition A B , f A k , g _ ∘ ks

Constant : ℕ → TypeOfHLevel ℓ₂ (suc i) → Species (suc i) ℓ₁ ℓ₂
Constant n A X with discreteℕ n (card X)
... | yes p = A
... | no ¬p = Lift ⊥ , isProp→isOfHLevelSuc _ λ ()

⊚-Unit : Species 1 ℓ₁ ℓ₂
⊚-Unit = Constant {i = 0} 1 (Lift ⊤ , λ { (lift tt) (lift tt) → refl })

