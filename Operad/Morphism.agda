{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Morphism where

open import Cubical.Data.Sigma hiding (comp)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Prelude hiding (comp)

open import Operad.Base
  
private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ : Level
    O₁ : Operad ℓ₁ ℓ₂
    O₂ : Operad ℓ₁ ℓ₃
    O₃ : Operad ℓ₁ ℓ₄

open Operad

record _⇒ᵒᵖ_ (O₁ : Operad ℓ₁ ℓ₂) (O₂ : Operad ℓ₁ ℓ₃) : Type (ℓ-suc (ℓ-max ℓ₁ (ℓ-max ℓ₂ ℓ₃))) where
  field
    ⟪_⟫     : ∀ {A} → Ops O₁ A → Ops O₂ A
    id-resp : ⟪ id O₁ ⟫ ≡ id O₂
    ∘-resp  : ∀ A B a b → ⟪ comp O₁ A B a b ⟫ ≡ comp O₂ A B ⟪ a ⟫ (⟪_⟫ ∘ b)

open _⇒ᵒᵖ_

idᵒᵖ : (O : Operad ℓ₁ ℓ₂) → O ⇒ᵒᵖ O
⟪ idᵒᵖ O ⟫ k            = k
id-resp (idᵒᵖ O)        = refl
∘-resp (idᵒᵖ O) _ _ _ _ = refl

_∘ᵒᵖ_ : O₂ ⇒ᵒᵖ O₃ → O₁ ⇒ᵒᵖ O₂ → O₁ ⇒ᵒᵖ O₃
⟪ g ∘ᵒᵖ f ⟫                = ⟪ g ⟫ ∘ ⟪ f ⟫
id-resp (g ∘ᵒᵖ f)          = cong ⟪ g ⟫ (id-resp f) ∙ id-resp g
∘-resp  (g ∘ᵒᵖ f) A B k ks = cong ⟪ g ⟫ (∘-resp f A B k ks) ∙
                            ∘-resp g A B (⟪ f ⟫ k) (⟪ f ⟫ ∘ ks)

_⇒≡_ : (O₁ ⇒ᵒᵖ O₂) → (O₁ ⇒ᵒᵖ O₂) → Type _
f ⇒≡ g = ∀ A k → ⟪ f ⟫ {A} k ≡ ⟪ g ⟫ k

⇒≡→≡ : (f g : O₁ ⇒ᵒᵖ O₂) → f ⇒≡ g → f ≡ g
⟪ ⇒≡→≡ f g p i ⟫ k               = p _ k i
id-resp (⇒≡→≡ {O₂ = O₂} f g p i) =
  isProp→PathP (λ i → isSetOps O₂ _ (p _ _ i) (id O₂))
               (id-resp f) (id-resp g) i
∘-resp (⇒≡→≡ {O₂ = O₂} f g p i) A B a b =
  isProp→PathP (λ i → isSetOps O₂ _ (p _ _ i)
                                  (comp O₂ A B (p A a i) λ a → p (B a) (b a) i))
               (∘-resp f A B a b) (∘-resp g A B a b) i

open Iso

isSet⇒ᵒᵖ : isSet (O₁ ⇒ᵒᵖ O₂)
isSet⇒ᵒᵖ {O₂ = O₂} = isOfHLevelRetract 2
                      (inv ⇒ᵒᵖ-Σ)
                      (fun ⇒ᵒᵖ-Σ)
                      (rightInv ⇒ᵒᵖ-Σ)
                      (isSetΣ (isSetImplicitΠ λ _ → isSetΠ λ _ → isSetOps O₂ _)
                              λ f → isSetΣ (isProp→isSet (isSetOps O₂ _ _ _))
                              λ _ → isSetΠ λ _ → isSetΠ λ _ →
                                    isSetΠ λ _ → isSetΠ λ _ →
                                    isProp→isSet (isSetOps O₂ _ _ _))
  where
    isSetImplicitΠ : {A : Type ℓ₁} {B : A → Type ℓ₂} →
                     ((a : A) → isSet (B a)) → isSet ({a : A} → B a)
    isSetImplicitΠ h f g p q i j {a} =
      h a (f {a}) (g {a}) (λ k → p k) (λ k → q k) i j             

    ⇒ᵒᵖ-Σ : Iso (Σ[ ⟪_⟫ ∈ (∀ {A} → Ops O₁ A → Ops O₂ A) ]
                  (⟪ id O₁ ⟫ ≡ id O₂) ×
                  (∀ A B a b → ⟪ comp O₁ A B a b ⟫ ≡
                               comp O₂ A B ⟪ a ⟫ (⟪_⟫ ∘ b)))
                (O₁ ⇒ᵒᵖ O₂)
    ⟪ fun ⇒ᵒᵖ-Σ (f , i , c) ⟫ = f
    id-resp (fun ⇒ᵒᵖ-Σ (f , i , c)) = i
    ∘-resp  (fun ⇒ᵒᵖ-Σ (f , i , c)) = c
    inv ⇒ᵒᵖ-Σ f = ⟪ f ⟫ , id-resp f , ∘-resp f
    rightInv ⇒ᵒᵖ-Σ _ = refl
    leftInv ⇒ᵒᵖ-Σ _  = refl

open Iso

⇒ᵒᵖ-≃≡ : (f g : O₁ ⇒ᵒᵖ O₂) → (f ⇒≡ g) ≃ (f ≡ g)
⇒ᵒᵖ-≃≡ f g = _ , ⇒ᵒᵖ-isEquiv f g
  where
    ⇒ᵒᵖ-isEquiv : (f g : O₁ ⇒ᵒᵖ O₂) → isEquiv (⇒≡→≡ f g)
    equiv-proof (⇒ᵒᵖ-isEquiv {O₂ = O₂} f g) p =
      ((λ _ k i → ⟪ p i ⟫ k) , isSet⇒ᵒᵖ f g _ _) ,
        λ { (q , r) → isProp→PathP (λ i →
                        isPropΣ (isPropΠ2 λ _ _ → isSetOps O₂ _ _ _)
                                 λ _ → isContr→isProp
                                       (isProp→isContrPath (isSet⇒ᵒᵖ f g) _ _)) _ _ }

⇒ᵒᵖ-Iso≡ : (f g : O₁ ⇒ᵒᵖ O₂) → Iso (f ⇒≡ g) (f ≡ g)
fun      (⇒ᵒᵖ-Iso≡ f g)         = ⇒≡→≡ f g
inv      (⇒ᵒᵖ-Iso≡ f g) p A k i = ⟪ p i ⟫ k
rightInv (⇒ᵒᵖ-Iso≡ f g) p       = isSet⇒ᵒᵖ f g _ _
leftInv  (⇒ᵒᵖ-Iso≡ f g) _       = refl
