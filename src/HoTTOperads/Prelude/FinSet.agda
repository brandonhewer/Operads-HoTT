{-# OPTIONS --cubical #-}
module HoTTOperads.Prelude.FinSet where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.Structure
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Data.FinSet.Base public using (FinSet ; isFinSet ; isFinSet→isSet ; isPropIsFinSet)
open import Cubical.Data.FinSet.Properties public
open import Cubical.Data.FinSet.Constructors public using (isFinSetΣ ; isFinSetΠ ; isFinSet⊎)
open import Cubical.Data.Sigma

private
  variable
    ℓ : Level

-- The carrier of a FinSet.
El : FinSet ℓ → Type ℓ
El A = fst A

opaque
  -- Univalence-style identity: an equivalence between underlying types lifts to a path on FinSet.
  -- Since isFinSet is a proposition, two FinSets are equal iff their underlying types are.
  un : (A B : FinSet ℓ) → El A ≃ El B → A ≡ B
  un A B e = Σ≡Prop (λ _ → isPropIsFinSet) (ua e)

  -- General helpers for Σ-types with proposition fibres. Both follow directly from
  -- Σ≡PropEquiv pp : (u.fst ≡ v.fst) ≃ (u ≡ v), whose forward direction is Σ≡Prop pp
  -- and whose inverse is cong fst.

  cong-fst-Σ≡Prop : ∀ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
                    (pp : (x : A) → isProp (B x))
                    {u v : Σ A B}
                    (p : u .fst ≡ v .fst)
                  → cong fst (Σ≡Prop pp {u = u} {v = v} p) ≡ p
  cong-fst-Σ≡Prop pp {u} {v} p = retEq (Σ≡PropEquiv pp {u = u} {v = v}) p

  Σ≡Prop-∙ : ∀ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
             (pp : (x : A) → isProp (B x))
             {u v w : Σ A B}
             (p : u .fst ≡ v .fst) (q : v .fst ≡ w .fst)
           → Σ≡Prop pp {u = u} {v = w} (p ∙ q)
           ≡ Σ≡Prop pp {u = u} {v = v} p ∙ Σ≡Prop pp {u = v} {v = w} q
  Σ≡Prop-∙ pp {u} {v} {w} p q =
      sym (secEq (Σ≡PropEquiv pp {u = u} {v = w})
                 (Σ≡Prop pp {u = u} {v = w} (p ∙ q)))
    ∙ cong (Σ≡Prop pp {u = u} {v = w}) eqFst
    ∙ secEq (Σ≡PropEquiv pp {u = u} {v = w})
            (Σ≡Prop pp {u = u} {v = v} p ∙ Σ≡Prop pp {u = v} {v = w} q)
    where
      eqFst : cong fst (Σ≡Prop pp {u = u} {v = w} (p ∙ q))
            ≡ cong fst (Σ≡Prop pp {u = u} {v = v} p ∙ Σ≡Prop pp {u = v} {v = w} q)
      eqFst =
          cong-fst-Σ≡Prop pp {u = u} {v = w} (p ∙ q)
        ∙ cong₂ _∙_ (sym (cong-fst-Σ≡Prop pp {u = u} {v = v} p))
                    (sym (cong-fst-Σ≡Prop pp {u = v} {v = w} q))
        ∙ sym (cong-∙ fst (Σ≡Prop pp {u = u} {v = v} p)
                          (Σ≡Prop pp {u = v} {v = w} q))

  -- Symmetry of Σ≡Prop: `sym` and `Σ≡Prop` commute (modulo `sym` on the
  -- first-projection path). Same round-trip strategy as Σ≡Prop-∙.
  Σ≡Prop-sym : ∀ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
               (pp : (x : A) → isProp (B x))
               {u v : Σ A B}
               (p : u .fst ≡ v .fst)
             → sym (Σ≡Prop pp {u = u} {v = v} p)
             ≡ Σ≡Prop pp {u = v} {v = u} (sym p)
  Σ≡Prop-sym pp {u} {v} p =
      sym (secEq (Σ≡PropEquiv pp {u = v} {v = u})
                 (sym (Σ≡Prop pp {u = u} {v = v} p)))
    ∙ cong (Σ≡Prop pp {u = v} {v = u}) eqFst
    where
      eqFst : cong fst (sym (Σ≡Prop pp {u = u} {v = v} p)) ≡ sym p
      eqFst = cong sym (cong-fst-Σ≡Prop pp {u = u} {v = v} p)

  -- Injectivity of `cong fst` for Σ-types with propositional second factor.
  -- Two paths in (Σ A B) (with B prop) agree iff their first projections do.
  Σ≡Prop-inj : ∀ {ℓa ℓb} {A : Type ℓa} {B : A → Type ℓb}
               (pp : (x : A) → isProp (B x))
               {u v : Σ A B}
               (q₁ q₂ : u ≡ v)
             → cong fst q₁ ≡ cong fst q₂
             → q₁ ≡ q₂
  Σ≡Prop-inj pp {u} {v} q₁ q₂ h =
      sym (secEq (Σ≡PropEquiv pp {u = u} {v = v}) q₁)
    ∙ cong (Σ≡Prop pp {u = u} {v = v}) h
    ∙ secEq (Σ≡PropEquiv pp {u = u} {v = v}) q₂

  -- `un` commutes with `sym`/`invEquiv`: reversing a univalence-style FinSet
  -- path corresponds to taking the inverse equivalence.
  un-sym : (X Y : FinSet ℓ) (e : El X ≃ El Y)
         → sym (un X Y e) ≡ un Y X (invEquiv e)
  un-sym X Y e =
      Σ≡Prop-sym (λ _ → isPropIsFinSet) {u = X} {v = Y} (ua e)
    ∙ cong (Σ≡Prop (λ _ → isPropIsFinSet) {u = Y} {v = X}) (sym (uaInvEquiv e))
