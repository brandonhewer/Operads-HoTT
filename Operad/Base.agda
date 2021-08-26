{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Base where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude hiding (comp)

open import Operad.FinSet
open import Operad.FinSet.Small
open import Operad.Fin

private
  variable
    ℓ₁ ℓ₂ u p : Level
    U : Type u
    P : U → Type p

record Operad (ℓ₁ ℓ₂ : Level) : Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂)) where
  field
    Ops      : FinSetD ℓ₁ → Type ℓ₂
    isSetOps : ∀ A → isSet (Ops A) 
    id       : Ops ⊤F
    comp     : ∀ A B → Ops A → (∀ a → Ops (B a)) → Ops (ΣF A B)
    idl      : ∀ A k → PathP (λ i → Ops (ΣIdL A i))
                             (comp ⊤F A id k) (k _)
    idr      : ∀ A k → PathP (λ i → Ops (ΣIdR A i))
                             (comp A (const ⊤F) k (const id)) k
    assoc    : ∀ A B C k ks kss →
                 PathP (λ i → Ops (ΣAssoc A B C i))
                       (comp (ΣF A B) (uncurry C) (comp A B k ks) (uncurry kss))
                       (comp A (λ a → ΣF (B a) (C a)) k
                             λ a → comp (B a) (C a) (ks a) (kss a))

open import Cubical.Data.Sigma hiding (comp)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Equiv

open Iso

ΣIdLIsoT : {A : Lift {j = ℓ₂} ⊤ → Type ℓ₁} →
           Iso (Σ (Lift ⊤) A) (A _)
fun      ΣIdLIsoT (_ , a) = a
inv      ΣIdLIsoT a               = _ , a
rightInv ΣIdLIsoT _               = refl
leftInv  ΣIdLIsoT (_ , a) = refl

ΣIdRIsoT : {A : Type ℓ₁} →
           Iso (Σ A λ _ → Lift {j = ℓ₂} ⊤) A
fun      ΣIdRIsoT (a , _) = a
inv      ΣIdRIsoT a               = a , _
rightInv ΣIdRIsoT _               = refl
leftInv  ΣIdRIsoT (a , _) = refl

{-
record OperadF (ΣIdL : (A : Lift {j = ℓ₁} ⊤ → Type ℓ₁) → Σ (Lift ⊤) A ≡ A _)
               (ΣIdR : (A : Type ℓ₁) → Σ A (λ _ → Lift {j = ℓ₁} ⊤) ≡ A)
               (ΣAssoc : (A : Type ℓ₁) (B : A → Type ℓ₁)
                         (C : ∀ a → B a → Type ℓ₁) →
                         Σ (Σ A B) (uncurry C) ≡ Σ A λ a → Σ (B a) (C a))
               (ℓ₁ ℓ₂ : Level) : Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-suc ℓ₂)) where
  field
    Ops      : FinSet ℓ₁ → Type ℓ₂
    isSetOps : ∀ A → isSet (Ops A) 
    id       : Ops ?
    comp     : ∀ A B → Ops A → (∀ a → Ops (B a)) → Ops (ΣF A B)
    idl      : ∀ A k → PathP (λ i → Ops (ΣIdL A i))
                             (comp ⊤F A id k) (k _)
    idr      : ∀ A k → PathP (λ i → Ops (ΣIdR A i))
                             (comp A (const ⊤F) k (const id)) k
    assoc    : ∀ A B C k ks kss →
                 PathP (λ i → Ops (ΣAssoc A B C i))
                       (comp (ΣF A B) (uncurry C) (comp A B k ks) (uncurry kss))
                       (comp A (λ a → ΣF (B a) (C a)) k
                             λ a → comp (B a) (C a) (ks a) (kss a))
-}

record OperadT {U : Type ℓ₁} (P : U → Type ℓ₂) (ℓ₃ : Level)
             : Type (ℓ-max ℓ₁ (ℓ-suc (ℓ-max ℓ₂ ℓ₃))) where
  field
    Ops : FinClosure P → Type ℓ₃
    isSetOps : ∀ A → isSet (Ops A)
    id : Ops ⊤F
    comp : ∀ A B → Ops A → (∀ a → Ops (B a)) → Ops (ΣF A B)
    idl      : ∀ A k → PathP (λ i → Ops (ΣIdL A i))
                             (comp ⊤F A id k) (k _)
    idr      : ∀ A k → PathP (λ i → Ops (ΣIdR A i))
                             (comp A (const ⊤F) k (const id)) k
    assoc    : ∀ A B C k ks kss →
                 PathP (λ i → Ops (ΣAssoc A B C i))
                       (comp (ΣF A B) (uncurry C) (comp A B k ks) (uncurry kss))
                       (comp A (λ a → ΣF (B a) (C a)) k
                             λ a → comp (B a) (C a) (ks a) (kss a))

OperadTy : (ℓ₁ ℓ₂ : Level) → Type _
OperadTy ℓ₁ ℓ₂ = OperadT {ℓ₂ = ℓ₁} (λ A → A) ℓ₂

open Operad
open OperadT

private
  variable
    ℓ₃ : Level

-- Extend (Ops O) (Σ (El A) B)

module _ {ℓ₁ : Level} where

  open import Cubical.Foundations.Univalence.Universe (FinSetD ℓ₁) El un (λ _ → refl)

  ToOperadT : Operad ℓ₁ ℓ₂ → OperadTy ℓ₁ _
  Ops (ToOperadT O) A = Σ[ p ∈ isFinite (El A) ] Ops O (Ty (El A , p))
  isSetOps (ToOperadT O) = {!!}
  id (ToOperadT O) = {!!}
  comp (ToOperadT O) = {!!}
  idl (ToOperadT O) = {!!}
  idr (ToOperadT O) = {!!}
  assoc (ToOperadT O) = {!!}

  {-
  ToOperadT : Operad ℓ₁ ℓ₂ → OperadTy ℓ₁ _
  Ops (ToOperadT O) A = Σ[ p ∈ isFinite A ] Ops O (Ty (A , p))
  isSetOps (ToOperadT O) A = isSetΣ (isProp→isSet isPropIsFinite) λ p → isSetOps O _
  id (ToOperadT O) = isFinite-⊤ , subst (Ops O) (un _ _ (idEquiv _)) (id O)
  comp (ToOperadT O) A B (p , f) gqs =
    isFiniteΣ p (fst ∘ gqs) ,
    subst (Ops O) (un _ _ (idEquiv _)) (comp O _ _ f (snd ∘ gqs))
  idl (ToOperadT O) A k =
    ΣPathP (
      p ,
      {!!}
    )
    where
      p : PathP (λ i → isFinite (isoToPath ΣIdLIsoT i))
                (isFiniteΣ isFinite-⊤ (fst ∘ k)) (fst (k _))
      p = isProp→PathP (λ i → isPropIsFinite {X = isoToPath ΣIdLIsoT i}) _ _

      q : comp O _ _ (subst (Ops O) (un ⊤F (Ty (_ , isFinite-⊤))
                            (idEquiv _)) (id O)) (snd ∘ k) ≡
          subst (Ops O) (un _ _ (idEquiv _)) (comp O _ _ (id O) (snd ∘ k))
      q = {!!}
  -}    

-- isProp→PathP (λ i → isPropIsFinite {X = isoToPath ΣIdLIsoT i}) _ _
   
       {-
   PathP
      (λ i →
         Ops O
         (Ty
          (isoToPath ΣIdLIsoT i ,
           isProp→PathP (λ i₁ → isPropIsFinite)
           (isFiniteΣ isFinite-⊤ (λ x → fst (k x))) (fst (k tt*)) i)))
      (subst (Ops O)
       (un (ΣF (Ty (Lift ⊤ , isFinite-⊤)) (λ z → Ty (A z , fst (k z))))
        (Ty (Σ (Lift ⊤) A , isFiniteΣ isFinite-⊤ (λ x → fst (k x))))
        (idEquiv (Σ (Lift ⊤) A)))
       (comp O (Ty (Lift ⊤ , isFinite-⊤)) (λ z → Ty (A z , fst (k z)))
        (subst (Ops O)
         (un ⊤F (Ty (Lift ⊤ , isFinite-⊤)) (idEquiv (Lift ⊤))) (id O))
        (λ x → snd (k x))))
      (snd (k tt*))-}


{-
   PathP
      (λ i →
         Ops O
         (Ty
          (isoToPath ΣIdLIsoT i ,
           isProp→PathP (λ i₁ → isPropIsFinite)
           (isFiniteΣ isFinite-⊤ (λ x → fst (k x))) (fst (k tt*)) i)))
      (subst (Ops O)
       (un (ΣF (Ty (Lift ⊤ , isFinite-⊤)) (λ z → Ty (A z , fst (k z))))
        (Ty (Σ (Lift ⊤) A , isFiniteΣ isFinite-⊤ (λ x → fst (k x))))
        (idEquiv (Σ (Lift ⊤) A)))
       (comp O (Ty (Lift ⊤ , isFinite-⊤)) (λ z → Ty (A z , fst (k z)))
        (subst (Ops O)
         (un ⊤F (Ty (Lift ⊤ , isFinite-⊤)) (idEquiv (Lift ⊤))) (id O))
        (λ x → snd (k x))))
      (snd (k tt*))
-}
-- snd (ks _)

--  isFinite (isoToPath ΣIdLIsoT i)

{-
PathP
      (λ i →
         Σ-syntax (isFinite (isoToPath ΣIdLIsoT i))
         (λ p → Ops O (Ty (isoToPath ΣIdLIsoT i , p))))
      (isFiniteΣ isFinite-⊤ (λ x → fst (k x)) ,
       subst (Ops O)
       (un (ΣF (Ty (Lift ⊤ , isFinite-⊤)) (λ z → Ty (A z , fst (k z))))
        (Ty (Σ (Lift ⊤) A , isFiniteΣ isFinite-⊤ (λ x → fst (k x))))
        (idEquiv (Σ ⟦ Lift ⊤ , isFinite-⊤ ⟧ (λ x → ⟦ A x , fst (k x) ⟧))))
       (comp O (Ty (Lift ⊤ , isFinite-⊤)) (λ z → Ty (A z , fst (k z)))
        (subst (Ops O)
         (un ⊤F (Ty (Lift ⊤ , isFinite-⊤)) (idEquiv (Lift ⊤))) (id O))
        (λ x → snd (k x))))
      (k tt*)
      -}

{-
ToOperadT : Operad ℓ₁ ℓ₂ → OperadTy ℓ₁ _
Ops (ToOperadT O) = Extend (Ops O)
isSetOps (ToOperadT O) = set/
id (ToOperadT O) = elem ⊤F (id O)
comp (ToOperadT O) .(El A) B (elem A x) xs =
  subst (Extend (Ops O)) {!!}
        (elem {!!} (comp O A {!!} x ({!!} ∘ xs)))
comp (ToOperadT O) A B (set/ .A x x₁ x₂ y i i₁) xs = {!!}
idl (ToOperadT O) = {!!}
idr (ToOperadT O) = {!!}
assoc (ToOperadT O) = {!!}
-}
