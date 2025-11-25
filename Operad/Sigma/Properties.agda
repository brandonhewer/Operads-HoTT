{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Sigma.Properties where

open import Cubical.Data.Sigma

open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Operad.Fin

private
  variable
    ℓ₁ ℓ₂ : Level
    A : Type ℓ₁
    B : A → Type ℓ₂

open Iso

isContrLift : isContr A → isContr (Lift {j = ℓ₂} A)
isContrLift (c , p) = lift c , λ { (lift y) → cong lift (p y) }

Σ-contractFst-Iso : (c : isContr A) → Iso (Σ A B) (B (c .fst))
Σ-contractFst-Iso {B = B} (c , p) = isom
  where
    isom : Iso _ _
    fun      isom (a , b) = subst B (sym (p a)) b
    inv      isom b       = c , b
    rightInv isom b       =
      cong (λ p → subst B p b)
           (isProp→isSet (isContr→isProp (c , p)) _ _ _ _) ∙
      transportRefl _
    leftInv  isom (a , b) =
      ΣPathTransport≃PathΣ _ _ .fst (p a , transportTransport⁻ (cong B (p a)) _)

Σ-contractSnd-Iso : ((a : A) → isContr (B a)) → Iso (Σ A B) A
fun      (Σ-contractSnd-Iso f) (a , b) = a
inv      (Σ-contractSnd-Iso f) a       = a , f a .fst
rightInv (Σ-contractSnd-Iso f) a       = refl
leftInv  (Σ-contractSnd-Iso f) (a , b) = cong (a ,_) (f a .snd b)

Σ-Idl : Iso (Σ[ i ∈ Lift {j = ℓ₂} (Fin 1) ] A) A
Σ-Idl = Σ-contractFst-Iso (isContrLift isContrFin1)

Σ-Idr : Iso (Σ[ a ∈ A ] (Lift {j = ℓ₂} (Fin 1))) A
Σ-Idr = Σ-contractSnd-Iso (const (isContrLift isContrFin1))
