{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Morphism where

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude hiding (comp)

open import Operad.Base
open import Operad.FinSet.Small

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
