{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.FinSet.Properties where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Nat hiding (snotz; znots)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.HITs.PropositionalTruncation renaming (rec to p-rec)

open import Cubical.Relation.Nullary

open import Operad.Fin
open import Operad.FinSet.Base
open import Operad.Sigma

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    X : Type ℓ₁
    Y : Type ℓ₂
    Z : Type ℓ₄
    W : X → Type ℓ₂

  open Iso

  p-rec₂ : {P : Type ℓ₃} → isProp P → (X → Y → P) → ∥ X ∥ → ∥ Y ∥ → P
  p-rec₂ p f x y = p-rec p (λ x → p-rec p (f x) y) x

  compIso⁻ : Iso X Y → Iso X Z → Iso Y Z
  compIso⁻ I₁ I₂ = compIso (invIso I₁) I₂

  sameSize : ∀ m n → Iso X (Fin m) → Iso X (Fin n) → m ≡ n
  sameSize m n I₁ I₂ = Fin-inj (compIso⁻ I₁ I₂)

  transportInv : {A₁ A₂ : Type ℓ₁} (I : Iso A₁ A₂) → ∀ a → inv I a ≡ transport⁻ (isoToPath I) a
  transportInv I a = cong (inv I) (sym (transportRefl _))

  iso→substPath : {A₁ A₂ : Type ℓ₁} {B₁ : A₁ → Type ℓ₃} {B₂ : A₂ → Type ℓ₃} →
                  (I : Iso A₁ A₂) → ((a : A₂) → Iso (B₁ (inv I a)) (B₂ a)) →
                  subst (λ A → A → Type ℓ₃) (isoToPath I) B₁ ≡ B₂
  iso→substPath {B₁ = B₁} {B₂ = B₂} I Is =
    funExt λ a → isoToPath (subst (λ x → Iso (B₁ x) (B₂ a)) (transportInv I a) (Is a))

  iso-cong-path : {A₁ A₂ : Type ℓ₁} {B₁ : A₁ → Type ℓ₂} {B₂ : A₂ → Type ℓ₂} →
                  (I : Iso A₁ A₂) → ((a : A₂) → Iso (B₁ (inv I a)) (B₂ a)) →
                  PathP (λ i → isoToPath I i → Type ℓ₂) B₁ B₂
  iso-cong-path {B₁ = B₁} I Is = transport⁻ (PathP≡Path _ _ _) (iso→substPath {B₁ = B₁} I Is)

  congIso₂ : (_∙_ : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ-max ℓ₁ ℓ₂))
             {A₁ A₂ : Type ℓ₁} {B₁ : A₁ → Type ℓ₃} {B₂ : A₂ → Type ℓ₃} →
             (I : Iso A₁ A₂) → ((a : A₂) → Iso (B₁ (inv I a)) (B₂ a)) →
             Iso (A₁ ∙ B₁) (A₂ ∙ B₂)
  congIso₂ _∙_ I Is =
    pathToIso (cong₂ _∙_ (isoToPath I) (iso-cong-path I Is))

  isOfHLevelRespectIso : ∀ n → Iso X Y → isOfHLevel n X → isOfHLevel n Y
  isOfHLevelRespectIso n I p = isOfHLevelRetract n (inv I) (fun I) (rightInv I) p

  inv≡inv→b₁≡b₂ : (I : Iso X Y) → ∀ {x₁ x₂} → inv I x₁ ≡ inv I x₂ → x₁ ≡ x₂
  inv≡inv→b₁≡b₂ I {x₁} {x₂} p =
    x₁               ≡⟨ sym (rightInv I x₁) ⟩
    fun I (inv I x₁) ≡⟨ cong (fun I) p ⟩
    fun I (inv I x₂) ≡⟨ rightInv I x₂ ⟩
    x₂               ∎

  discreteRespectsIso : Iso X Y → Discrete X → Discrete Y
  discreteRespectsIso I Dₓ y₁ y₂ with Dₓ (inv I y₁) (inv I y₂)
  discreteRespectsIso I Dₓ y₁ y₂ | yes p = yes (inv≡inv→b₁≡b₂ I p)
  discreteRespectsIso I Dₓ y₁ y₂ | no ¬p = no (¬p ∘ cong (inv I))

  Finite→Discrete : ∀ {n} {x y : X} → Iso X (Fin n) → Dec (x ≡ y)
  Finite→Discrete I = discreteRespectsIso (invIso I) discreteFin _ _

  ContrIso : isContr X → isContr Y → Iso X Y
  fun      (ContrIso (x , p) (y , q)) = const y
  inv      (ContrIso (x , p) (y , q)) = const x
  rightInv (ContrIso (x , p) (y , q)) = q
  leftInv  (ContrIso (x , p) (y , q)) = p

  Inj→¬Iso : (f : X → Y) → (∀ x y → f x ≡ f y → x ≡ y) → ∀ x y → Iso (¬ x ≡ y) (¬ f x ≡ f y)
  fun      (Inj→¬Iso f g x y) ¬p p = ¬p (g x y p)
  inv      (Inj→¬Iso f g x y) ¬p p = ¬p (cong f p)
  rightInv (Inj→¬Iso f g x y) _    = isProp¬ _ _ _
  leftInv  (Inj→¬Iso f g x y) _    = isProp¬ _ _ _

  ¬Iso0 : Iso X (Fin 0) → Iso (¬ X) (Fin 1)
  fun      (¬Iso0 I) _    = zero
  inv      (¬Iso0 I) _ x  = ¬Fin0 (fun I x)
  rightInv (¬Iso0 I) zero = refl
  leftInv  (¬Iso0 I) _    = isPropΠ (λ _ → isProp⊥) _ _

  ¬Iso-suc : ∀ {n} → Iso X (Fin (suc n)) → Iso (¬ X) (Fin 0)
  fun      (¬Iso-suc I) f = ⊥-rec (f (inv I zero))
  inv      (¬Iso-suc I) i = ⊥-rec (¬Fin0 i)
  rightInv (¬Iso-suc I) _ = isPropFin0 _ _
  leftInv  (¬Iso-suc I) _ = isPropΠ (λ _ → isProp⊥) _ _

isContr→≡Fin1 : isContr X → X ≡ Lift (Fin 1)
isContr→≡Fin1 p = isoToPath (ContrIso p (lift _ , λ { (lift zero) → refl }))

uniqueSize : (p q : isFinite X) → p .fst ≡ q .fst
uniqueSize (m , p) (n , q) = p-rec₂ (isSetℕ m n) (sameSize m n) p q

isPropIsFinite : isProp (isFinite X)
isPropIsFinite x y = Σ≡Prop (λ _ → propTruncIsProp) (uniqueSize x y)

isFinite→isSet : isFinite X → isSet X
isFinite→isSet (_ , p) = p-rec isPropIsSet (λ I → isOfHLevelRespectIso 2 (invIso I) isSetFin) p

isSetFinSet : (A : FinSet ℓ₁) → isSet ⟦ A ⟧
isSetFinSet (_ , p) = isFinite→isSet p

isFinite→Discrete : isFinite X → Discrete X
isFinite→Discrete q@(_ , p) x y = p-rec (isPropDec (isFinite→isSet q x y)) Finite→Discrete p

isDiscreteFinSet : (A : FinSet ℓ₁) → Discrete ⟦ A ⟧
isDiscreteFinSet (_ , p) = isFinite→Discrete p

isCardPropInj : (A : FinSet ℓ₁) (B : FinSet ℓ₂) → card A ≡ card B → ∥ Iso ⟦ A ⟧ ⟦ B ⟧ ∥
isCardPropInj A B p = rec A propTruncIsProp λ I₁ →
                      rec B propTruncIsProp λ I₂ →
                      ∣ compIso (subst (λ n → Iso ⟦ A ⟧ (Fin n)) p I₁) (invIso I₂) ∣

¬isCardPropInj : (A : FinSet ℓ₁) (B : FinSet ℓ₂) → ¬ card A ≡ card B → ¬ ∥ Iso ⟦ A ⟧ ⟦ B ⟧ ∥
¬isCardPropInj A B p = rec A (isPropΠ λ _ ()) λ I₁ →
                       rec B (isPropΠ λ _ ()) λ I₂ →
                       p-rec (λ ()) λ I →
                       p (Fin-inj (compIso (invIso I₁) (compIso I I₂)))

Lift≡ : (A₁ A₂ : FinSet ℓ₁) → ⟦ A₁ ⟧ ≡ ⟦ A₂ ⟧ → A₁ ≡ A₂
Lift≡ A₁ A₂ p = Σ≡Prop (λ _ → isPropIsFinite) p

Lower≡ : (A₁ A₂ : FinSet ℓ₁) → A₁ ≡ A₂ → ⟦ A₁ ⟧ ≡ ⟦ A₂ ⟧
Lower≡ A₁ A₂ p i = fst (p i)

LiftLower≃ : (A₁ A₂ : FinSet ℓ₁) → (⟦ A₁ ⟧ ≡ ⟦ A₂ ⟧) ≃ (A₁ ≡ A₂)
LiftLower≃ A₁ A₂ = Σ≡PropEquiv λ _ → isPropIsFinite

isGroupoidFinSet : isGroupoid (FinSet ℓ₁)
isGroupoidFinSet A B = isOfHLevelRespectEquiv 2 (LiftLower≃ A B)
                                                (isOfHLevel≡ 2 (isSetFinSet A) (isSetFinSet B))

Card1→isContr : (A : FinSet ℓ₁) → 1 ≡ card A → isContr ⟦ A ⟧
Card1→isContr A p = rec A isPropIsContr λ I →
                          isOfHLevelRespectIso 0 (invIso I)
                            (subst (isContr ∘ Fin) p isContrFin1)

Card1→≡⊤ : {A : FinSet ℓ₁} → 1 ≡ card A → A ≡ ⊤-FinSet ℓ₁
Card1→≡⊤ {A = A} p = Lift≡ _ _ (isContr→≡Fin1 (Card1→isContr A p))

ContrFinSet₁ : isContr (Σ[ A ∈ FinSet ℓ₁ ] 1 ≡ card A)
ContrFinSet₁ = (⊤-FinSet _ , refl) , λ { (_ , p) → Σ≡Prop (λ _ → isSetℕ _ _) (sym (Card1→≡⊤ p)) }

isFiniteContr : isContr X → isFinite X
isFiniteContr (x , p) = 1 , ∣ iso (const zero) (const x) (λ { zero → refl }) (λ _ → p _) ∣

isFiniteEmpty : ¬ X → isFinite X
isFiniteEmpty ¬X = 0 , ∣ iso (⊥-rec ∘ ¬X) (λ ()) (λ ()) (⊥-rec ∘ ¬X) ∣

isFiniteDecProp : isProp X → Dec X → isFinite X
isFiniteDecProp isPropX (yes x) = isFiniteContr (x , isPropX _)
isFiniteDecProp isPropX (no ¬x) = isFiniteEmpty ¬x

isFiniteRemove : isFinite X → (x : X) → isFinite (Σ[ y ∈ X ] ¬ x ≡ y)
isFiniteRemove (zero , p)  x = p-rec isPropIsFinite (λ I → ⊥-rec (¬Fin0 (fun I x))) p
isFiniteRemove (suc n , p) x = n , p-rec propTruncIsProp (λ I →
    ∣ compIso (Σ-cong-iso I λ y → Inj→¬Iso (fun I) (isoFunInjective I) x y) (Fin/ n (fun I x)) ∣
  ) p

_/_ : (A : FinSet ℓ₁) (a : ⟦ A ⟧) → FinSet ℓ₁
(_ , p) / a = _ , isFiniteRemove p a

isFiniteFin≡ : isFinite X → (a b : X) → isFinite (a ≡ b)
isFiniteFin≡ isFiniteX a b with isFinite→Discrete isFiniteX a b
... | yes p = 1 , ∣ iso
                     (const zero)
                     (const p)
                     (λ { zero → refl })
                     (isFinite→isSet isFiniteX _ _ p)
                  ∣
... | no ¬p = 0 , ∣ iso (⊥-rec ∘ ¬p) (⊥-rec ∘ ¬Fin0) (⊥-rec ∘ ¬Fin0) (⊥-rec ∘ ¬p) ∣

_⟨_≡_⟩ : (A : FinSet ℓ₁) → ⟦ A ⟧ → ⟦ A ⟧ → FinSet ℓ₁
(_ , isFiniteA) ⟨ a ≡ b ⟩ = _ , isFiniteFin≡ isFiniteA a b

isFinite¬ : isFinite X → isFinite (¬ X)
isFinite¬ (zero  , p) = 1 , p-rec propTruncIsProp (∣_∣ ∘ ¬Iso0) p
isFinite¬ (suc n , p) = 0 , p-rec propTruncIsProp (∣_∣ ∘ ¬Iso-suc) p

_⟨_≢_⟩ : (A : FinSet ℓ₁) → ⟦ A ⟧ → ⟦ A ⟧ → FinSet ℓ₁
A ⟨ a ≢ b ⟩ = _ , isFinite¬ (isFiniteFin≡ (snd A) a b) -- (A ⟨ a ≡ b ⟩)

isFiniteClosure : (_∙_ : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ-max ℓ₁ ℓ₂)) →
                  (size : ∀ n (ns : Fin n → ℕ) → ℕ) →
                  (∀ m (ns : Fin m → ℕ) → Iso (Lift {j = ℓ₁} (Fin m) ∙
                                                (Lift {j = ℓ₂} ∘ Fin ∘ ns ∘ lower))
                                              (Fin (size m ns))) →
                  {X : Type ℓ₁} {Y : X → Type ℓ₂} →
                  isFinite X → (∀ x → isFinite (Y x)) → isFinite (X ∙ Y)
isFiniteClosure _∙_ size is (n , X↔Fin) isFiniteY =
  p-rec isPropIsFinite (λ I →
    size n (fst ∘ isFiniteY ∘ inv I) ,
    p-rec propTruncIsProp (λ Is →
      ∣
        compIso (congIso₂ _∙_ (compIso I LiftIso) (flip compIso LiftIso ∘ Is ∘ lower))
                (is n (fst ∘ isFiniteY ∘ inv I))
      ∣
    ) (finiteChoice n (snd ∘ isFiniteY ∘ inv I))
  ) X↔Fin

isFiniteClosure′ : (_∙_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ-max ℓ₁ ℓ₂)) →
                   (_+_ : ℕ → ℕ → ℕ) →
                   (∀ m n → Iso (Lift (Fin m) ∙ Lift (Fin n)) (Fin (m + n))) →
                   isFinite X → isFinite Y → isFinite (X ∙ Y)
isFiniteClosure′ _∙_ _+_ is (m , X↔Fin) (n , Y↔Fin) =
  m + n , p-rec₂ propTruncIsProp (λ Ix Iy →
    ∣
      compIso (congIso₂′ _∙_ (compIso Ix LiftIso)
                             (compIso Iy LiftIso))
              (is m n)
    ∣
  ) X↔Fin Y↔Fin

fromClosure : (_∙_ : ∀ {ℓ₁ ℓ₂} (A : Type ℓ₁) → (A → Type ℓ₂) → Type (ℓ-max ℓ₁ ℓ₂)) →
              (size : ∀ n (ns : Fin n → ℕ) → ℕ) →
              (∀ m (ns : Fin m → ℕ) → Iso (Lift (Fin m) ∙ (Lift ∘ Fin ∘ ns ∘ lower))
                                          (Fin (size m ns))) →
              (A : FinSet ℓ₁) → (⟦ A ⟧ → FinSet ℓ₂) → FinSet (ℓ-max ℓ₁ ℓ₂)
fromClosure _∙_ size ps (_ , isFiniteA) B =
  _ , isFiniteClosure _∙_ size ps isFiniteA (snd ∘ B)

fromClosure′ : (_∙_ : ∀ {ℓ₁ ℓ₂} → Type ℓ₁ → Type ℓ₂ → Type (ℓ-max ℓ₁ ℓ₂)) →
               (_+_ : ℕ → ℕ → ℕ) →
               (∀ m n → Iso (Lift (Fin m) ∙ Lift (Fin n)) (Fin (m + n))) →
               FinSet ℓ₁ → FinSet ℓ₂ → FinSet (ℓ-max ℓ₁ ℓ₂)
fromClosure′ _∙_ _+_ is (_ , isFiniteA) (_ , isFiniteB) =
  _ , isFiniteClosure′ _∙_ _+_ is isFiniteA isFiniteB

finiteProp : (P : FinSet ℓ₁ → Type ℓ₂) → (∀ A → isProp (P A)) →
             (∀ n → P (n-FinSet n)) → ∀ A → P A
finiteProp P isPropP f A =
  rec A (isPropP A) λ I →
    let Fin≡A = sym (Lift≡ A (n-FinSet (card A)) (isoToPath (compIso I LiftIso)))
     in subst P Fin≡A (f (card A))

finiteProp₂ : (P : (A : FinSet ℓ₁) (B : ⟦ A ⟧ → FinSet ℓ₁) → Type ℓ₂) →
              (∀ A B → isProp (P A B)) →
              (∀ n ns → P (n-FinSet n) (n-FinSet ∘ ns ∘ lower)) → ∀ A B → P A B
finiteProp₂ P isPropP f =
  finiteProp (λ A → (∀ B → P A B)) (λ _ → isPropΠ λ _ → isPropP _ _) λ n B →
    let B↔Fin = finiteChoice n (Fin↔ ∘ B ∘ lift)
      in p-rec (isPropP _ _) (λ Is →
           let Fin≡B : ∀ i → n-FinSet (card (B i)) ≡ B i
               Fin≡B i = sym (Lift≡ _ _ (isoToPath (compIso (Is (lower i)) LiftIso)))
            in subst (P (n-FinSet n)) (funExt Fin≡B) (f n (card ∘ B ∘ lift))
         ) B↔Fin

finiteProp₃ : (P : (A : FinSet ℓ₁) (B : ⟦ A ⟧ → FinSet ℓ₁)
                     (C : ∀ a → ⟦ B a ⟧ → FinSet ℓ₁) → Type ℓ₂) →
              (∀ A B C → isProp (P A B C)) →
              (∀ n ns (nss : ∀ i → Fin (ns i) → ℕ) →
                 P (n-FinSet n) (n-FinSet ∘ ns ∘ lower)
                   (λ i j → n-FinSet (nss (lower i) (lower j)))) →
               ∀ A B C → P A B C
finiteProp₃ P isPropP f =
  finiteProp₂ (λ A B → ∀ C → P A B C) (λ _ _ → isPropΠ λ _ → isPropP _ _ _)
    λ n ns C →
      let C↔Fin = finiteChoice₂ n ns λ i j → Fin↔ (C (lift i) (lift j))
        in p-rec (isPropP _ _ _) (λ Is →
            let Fin≡C : ∀ i j → n-FinSet (card (C i j)) ≡ C i j
                Fin≡C i j =
                  sym (
                    Lift≡ _ _ (isoToPath (compIso (Is (lower i) (lower j)) LiftIso))
                  )
             in subst (P (n-FinSet n) (n-FinSet ∘ ns ∘ lower))
                      (λ i j k → Fin≡C j k i)
                      (f n ns λ i j → card (C (lift i) (lift j)))
           ) C↔Fin
