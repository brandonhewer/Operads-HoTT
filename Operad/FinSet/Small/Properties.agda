{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Small.Properties where

open import Cubical.Data.Bool
open import Cubical.Data.FinData
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding

open import Cubical.Relation.Nullary

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.FinSet.Properties hiding (_/_)
open import Operad.FinSet.Product
open import Operad.FinSet.Function
open import Operad.FinSet.Small.Base
open import Operad.Sigma

open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ u p : Level
    U : Type u
    P : U → Type p

open Iso

ΣIdLIso : {A : Lift {j = ℓ₂} ⊤ → Type ℓ₁} →
          Iso (Σ (Lift ⊤) A) (A _)
fun      ΣIdLIso (_ , a) = a
inv      ΣIdLIso a       = _ , a
rightInv ΣIdLIso _        = refl
leftInv  ΣIdLIso (_ , a) = refl

ΣIdRIso : {A : Type ℓ₁} →
          Iso (Σ A λ _ → Lift {j = ℓ₂} ⊤) A
fun      ΣIdRIso (a , _) = a
inv      ΣIdRIso a       = a , _
rightInv ΣIdRIso _       = refl
leftInv  ΣIdRIso (a , _) = refl

FinSetD : ∀ ℓ → Type (ℓ-suc ℓ)
FinSetD ℓ = FinClosure {ℓ₂ = ℓ} ⟦_⟧

FinD : ℕ → FinSetD ℓ-zero
FinD n = Ty (Fin n , n , ∣ idIso ∣)

BoolD : FinSetD ℓ-zero
BoolD = Ty (Bool , 2 , ∣ Bool↔Fin2 ∣)
  where
    Bool↔Fin2 : Iso Bool (Fin 2)
    fun      Bool↔Fin2 = if_then suc zero else zero
    inv      Bool↔Fin2 = λ { zero → false; (suc zero) → true }
    rightInv Bool↔Fin2 = λ { zero → refl; (suc zero) → refl }
    leftInv  Bool↔Fin2 = λ { false → refl; true → refl }

ΣIdL : (A : El {P = P} ⊤F → FinClosure P) → ΣF ⊤F A ≡ A _
ΣIdL A = un _ _ (isoToEquiv ΣIdLIso)

ΣIdR : (A : FinClosure P) → ΣF A (λ _ → ⊤F) ≡ A
ΣIdR A = un _ _ (isoToEquiv ΣIdRIso)

ΣAssoc : (A : FinClosure P) (B : El A → FinClosure P)
         (C : ∀ a → El (B a) → FinClosure P) →
         ΣF (ΣF A B) (uncurry C) ≡ ΣF A λ a → ΣF (B a) (C a)
ΣAssoc A B C = un _ _ (isoToEquiv Σ-assoc-Iso)

≃-FinSet≡ : {A B : FinSetD ℓ₁} (p q : A ≡ B) →
            pathToEquiv (cong El p) .fst ≡ pathToEquiv (cong El q) .fst →
            p ≡ q
≃-FinSet≡ {ℓ₁} {A} {B} p q r =
  equiv-proof (isEquiv→isEmbedding (isEmbeddingEl A B) p q)
              (invEq (congEquiv univalence) (Σ≡Prop isPropIsEquiv r))
              .fst .fst
  where open import Cubical.Foundations.Univalence.Universe (FinSetD ℓ₁) El un (λ _ → refl)

ΣIdr-ΣAssoc-lem :
  (A : FinSetD ℓ₁) (B : El A → FinSetD ℓ₁) →
  cong (ΣF A) (funExt (sym ∘ ΣIdR ∘ B)) ≡
  sym (ΣIdR (ΣF A B)) ∙ ΣAssoc A B (λ _ _ → ⊤F) 
ΣIdr-ΣAssoc-lem {ℓ₁} A B =
  ≃-FinSet≡ (cong (ΣF A) (funExt (sym ∘ ΣIdR ∘ B)))
            (sym (ΣIdR (ΣF A B)) ∙ ΣAssoc A B (λ _ _ → ⊤F))
            (r ∙ sym q)
  where
    q : pathToEquiv (cong El (sym (ΣIdR (ΣF A B)) ∙ ΣAssoc A B (λ _ _ → ⊤F))) .fst ≡
        λ { (a , b) → a , b , _ }
    q =
      funExt (λ a → transportRefl _) ∙
      λ { i (a , b) →
          transp (λ _ → El A) i (transp (λ _ → El A) i a) ,
          transp (λ j → El (B (transp (λ _ → El A) (i ∨ ~ j) (transp (λ _ → El A) i a))))
                 i (transp (λ j → El (B (transp (λ _ → El A) (i ∨ ~ j) a))) i b) , _ }

    r : pathToEquiv (cong El (cong (ΣF A) (funExt (sym ∘ ΣIdR ∘ B)))) .fst ≡
        λ { (a , b) → a , b , _ }
    r i (a , b) =
      transp (λ _ → El A) i a ,
      transp (λ j → El (B (transp (λ _ → El A) (i ∨ ~ j) a)))
             i (equivFun (idEquiv (El (B a))) b) , _

ΣAssoc-ΣIdr-lem : 
  (A : FinSetD ℓ₁) (B : El A → FinSetD ℓ₁) →
  cong (ΣF A) (funExt (ΣIdR ∘ B)) ≡
  sym (ΣAssoc A B (λ _ _ → ⊤F)) ∙ ΣIdR (ΣF A B)
ΣAssoc-ΣIdr-lem A B =
  cong sym (
    ΣIdr-ΣAssoc-lem A B ∙
    sym (symDistr (sym (ΣAssoc A B (λ _ _ → ⊤F))) (ΣIdR (ΣF A B)))
  )

ΣAssoc-ΣIdl′ :
  (B : Lift {j = ℓ₃} (Fin 1) → FinSetD ℓ₁) (C : ∀ a → El (B a) → FinSetD ℓ₂) →
  Σ (Σ[ i ∈ Lift (Fin 1) ] El (B i)) (El ∘ uncurry C) ≃
  Σ (El (B (lift zero))) (El ∘ C (lift zero))
ΣAssoc-ΣIdl′ B C = isoToEquiv isom
  where
    isom : Iso (Σ (Σ[ i ∈ Lift (Fin 1) ] El (B i)) (El ∘ uncurry C))
               (Σ (El (B (lift zero))) (El ∘ C (lift zero)))
    fun isom ((lift zero , b) , c) = b , c
    inv isom (b , c) = (lift zero , b) , c
    rightInv isom _ = refl
    leftInv isom ((lift zero , b) , c) = refl

_/_ : (A : FinClosure P) (a : El A) → FinClosure P
A / a = ΣF A (¬F ∘ ≡F A a)

record FinClosed {U : Type ℓ₁}
                 (P : U → Type ℓ₂)
                 (F : Type ℓ₂ → Type ℓ₃) : Type (ℓ-max ℓ₁ (ℓ-max (ℓ-suc ℓ₂) ℓ₃)) where
  field
    isPropF : ∀ x → isProp (F x)
    Ty-F    : ∀ u → F (P u)
    ⊥-F     : F (Lift (Fin 0))
    ⊤-F     : F (Lift ⊤)
    Σ-F     : ∀ {A B} → F A → (∀ a → F (B a)) → F (Σ A B)
    Π-F     : ∀ {A} {B : A → Type ℓ₂} → F A → (∀ a → F (B a)) → F (∀ a → B a)
    ≡-F     : ∀ {A} → F A → (a b : A) → F (a ≡ b)
    ¬-F     : ∀ {A} → F A → F (¬ A)

open FinClosed

fromClosed : {F : Type ℓ₂ → Type ℓ₃} →
             FinClosed P F → ∀ A → F (El {P = P} A)
fromClosed p (Ty u)           = Ty-F p u
fromClosed p ⊥F               = ⊥-F p
fromClosed p ⊤F               = ⊤-F p
fromClosed p (ΣF A B)         = Σ-F p (fromClosed p A) (fromClosed p ∘ B)
fromClosed p (ΠF A B)         = Π-F p (fromClosed p A) (fromClosed p ∘ B)
fromClosed p (≡F A a b)       = ≡-F p (fromClosed p A) a b
fromClosed p (¬F A)           = ¬-F p (fromClosed p A)
fromClosed p (un A₁ A₂ eq i)  =
  isProp→PathP (λ i → isPropF p (ua eq i))
               (fromClosed p A₁)
               (fromClosed p A₂) i

isSetFinClosure : (∀ u → isSet (P u)) → (A : FinClosure P) → isSet (El A)
isSetFinClosure isSetP = fromClosed (isSetFinClosed isSetP)
  where
   isSetFinClosed : (∀ u → isSet (P u)) → FinClosed P isSet
   isPropF (isSetFinClosed isSetP) x = isPropIsSet
   Ty-F (isSetFinClosed isSetP) u = isSetP u
   ⊥-F (isSetFinClosed isSetP) ()
   ⊤-F (isSetFinClosed isSetP) = isProp→isSet (isContr→isProp (isOfHLevelLift 0 isContrUnit))
   Σ-F (isSetFinClosed isSetP) = isSetΣ
   Π-F (isSetFinClosed isSetP) _ = isSetΠ
   ≡-F (isSetFinClosed isSetP) p a b = isProp→isSet (p a b)
   ¬-F (isSetFinClosed isSetP) _ = isProp→isSet (isProp¬ _)

isSetFinSetD : (A : FinSetD ℓ₁) → isSet (El A)
isSetFinSetD = isSetFinClosure isSetFinSet

isSetFinSetDEl≡ : (A B : FinSetD ℓ₁) → isSet (El A ≡ El B)
isSetFinSetDEl≡ A B = isOfHLevel≡ 2 (isSetFinSetD A) (isSetFinSetD B)

congEl-inj : {x y : FinClosure P} (p q : x ≡ y) → cong El p ≡ cong El q → p ≡ q
congEl-inj {P = P} {x} {y} p q r =
  fst (fst (equiv-proof (isEquiv→isEmbedding (isEmbeddingEl x y) p q) r))
  where open import Cubical.Foundations.Univalence.Universe (FinClosure P) El un (λ _ → refl)

isSetFinSetD≡ : (A B : FinSetD ℓ₁) → isSet (A ≡ B)
isSetFinSetD≡ {ℓ₁} A B = subst isSet (sym (ua path-reflection)) (isSetFinSetDEl≡ A B)
  where open import Cubical.Foundations.Univalence.Universe (FinSetD ℓ₁) El un (λ _ → refl)

module _ {U : Type ℓ₁} {P : U → Type ℓ₂} {F : Type ℓ₂ → Type ℓ₃} where

  open import Cubical.Foundations.Univalence.Universe (FinClosure P) El un (λ _ → refl)

  reflectIso : (F→U : ∀ A → F A → U) →
               (∀ A FA → P (F→U A FA) ≃ A) →
               FinClosed P F →
               Iso (FinClosure P) (Σ[ A ∈ Type ℓ₂ ] F A)
  fun      (reflectIso F→U F→U→P C) A        = El A , fromClosed C A
  inv      (reflectIso F→U F→U→P C) (A , FA) = Ty (F→U A FA)
  rightInv (reflectIso F→U F→U→P C) (A , FA) = Σ≡Prop (isPropF C) (ua (F→U→P A FA))
  leftInv  (reflectIso F→U F→U→P C) A        =
    un (Ty (F→U (El A) (fromClosed C A))) A
       (F→U→P (El A) (fromClosed C A))

isFinSetFinClosed : FinClosed {ℓ₂ = ℓ₂} ⟦_⟧ isFinite
isPropF  isFinSetFinClosed _ = isPropIsFinite
Ty-F     isFinSetFinClosed   = snd
⊥-F      isFinSetFinClosed   = isFinite-n 0
⊤-F      isFinSetFinClosed   = isFinite-⊤
Σ-F      isFinSetFinClosed   = isFiniteΣ
Π-F      isFinSetFinClosed   = isFiniteΠ
≡-F      isFinSetFinClosed   = isFiniteFin≡
¬-F      isFinSetFinClosed   = isFinite¬

FinSet↔FinSetD : ∀ ℓ → Iso (FinSetD ℓ) (FinSet ℓ)
FinSet↔FinSetD ℓ = reflectIso _,_ (λ _ _ → idEquiv _) isFinSetFinClosed
