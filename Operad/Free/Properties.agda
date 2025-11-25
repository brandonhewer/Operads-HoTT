{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Free.Properties where

open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Structure

open import Cubical.Data.FinData

open import Operad.Algebra
open import Operad.Base
open import Operad.FinSet.Small
open import Operad.Free.Base
open import Operad.Morphism

private
  variable
    ℓ₁ ℓ₂ ℓ₃ : Level

open Operad

interpret′ : (K : FinSetD ℓ₁ → Type ℓ₂) (O : Operad ℓ₁ ℓ₃) →
             (∀ A → K A → Ops O A) → ∀ A → Free K A → Ops O A
interpret′ K O f A (Op .A x) = f A x
interpret′ K O f .⊤F unit = id O
interpret′ K O f .(ΣF A B) (graft A B t ts) =
  comp O A B (interpret′ K O f A t) λ a → interpret′ K O f (B a) (ts a)
interpret′ K O f .(ΣIdL A i) (fidl A t i) =
  idl O A (λ a → interpret′ K O f (A a) (t a)) i
interpret′ K O f .(ΣIdR A i) (fidr A t i) =
  idr O A (interpret′ K O f A t) i
interpret′ K O f .(ΣAssoc A B C i) (fassoc A B C t ts tss i) =
  assoc O A B C (interpret′ K O f A t)
                (λ a → interpret′ K O f (B a) (ts a))
                (λ a b → interpret′ K O f (C a b) (tss a b)) i
interpret′ K O f A (set/ .A t₁ t₂ p₁ p₂ i j) =
  isSetOps O A (interpret′ K O f A t₁)
               (interpret′ K O f A t₂)
               (cong (interpret′ K O f A) p₁)
               (cong (interpret′ K O f A) p₂) i j

open _⇒ᵒᵖ_

interpret : (K : FinSetD ℓ₁ → Type ℓ₂) (O : Operad ℓ₁ ℓ₃) →
            (∀ A → K A → Ops O A) → FreeOperad K ⇒ᵒᵖ O
⟪ interpret K O f ⟫ t = interpret′ K O f _ t
id-resp (interpret K O f) = refl
∘-resp (interpret K O f) A B a b = refl

unique-interpret : (K : FinSetD ℓ₁ → Type ℓ₂) (O : Operad ℓ₁ ℓ₃)
                   (f : ∀ A → K A → Ops O A) →
                   (g : FreeOperad K ⇒ᵒᵖ O) →
                   (∀ A t → ⟪ g ⟫ (Op A t) ≡ f A t) →
                   g ⇒≡ interpret K O f
unique-interpret K O f g p A (Op .A x) = p A x
unique-interpret K O f g p .⊤F unit = id-resp g
unique-interpret K O f g p .(ΣF A B) (graft A B t ts) =
  ∘-resp g A B t ts ∙ cong₂ (comp O A B) (unique-interpret K O f g p A t)
                            (funExt λ a → unique-interpret K O f g p (B a) (ts a))
unique-interpret K O f g p .(ΣIdL A i) (fidl A t i) =
  isProp→PathP (λ i → isSetOps O (ΣIdL A i)
                                 (⟪ g ⟫ (fidl A t i))
                                 (idl O A (λ a → interpret′ K O f (A a) (t a)) i))
               (∘-resp g ⊤F A unit t ∙
                       λ j → comp O ⊤F A (id-resp g j) λ a → unique-interpret K O f g p (A a) (t a) j)
               (λ i → unique-interpret K O f g p (A (lift zero)) (t (lift zero)) i) i
unique-interpret K O f g p .(ΣIdR A i) (fidr A t i) =
  let q = unique-interpret K O f g p A t
   in isProp→PathP (λ i → isSetOps O (ΣIdR A i)
                                     (⟪ g ⟫ (fidr A t i))
                                     (idr O A (interpret′ K O f A t) i))
                   (∘-resp g A (λ _ → ⊤F) t (λ _ → unit) ∙
                           λ j → comp O A (λ _ → ⊤F) (q j) λ _ → id-resp g j)
                   q i
unique-interpret K O f g p .(ΣAssoc A B C i) (fassoc A B C t ts tss i) =
  let q = unique-interpret K O f g p A t

      qs : (a : El A) → _
      qs a = unique-interpret K O f g p (B a) (ts a)

      qss : (a : El A) (b : El (B a)) → _
      qss a b = unique-interpret K O f g p (C a b) (tss a b)

   in isProp→PathP (λ i → isSetOps O (ΣAssoc A B C i)
                                     (⟪ g ⟫ (fassoc A B C t ts tss i))
                                     (assoc O A B C
                                            (interpret′ K O f A t)
                                            (λ a → interpret′ K O f (B a) (ts a))
                                            (λ a b → interpret′ K O f (C a b) (tss a b)) i))
                   (∘-resp g (ΣF A B) (uncurry C) (graft A B t ts)
                    (uncurry tss)
                    ∙
                    (λ j →
                       comp O (ΣF A B) (uncurry C)
                       ((∘-resp g A B t ts ∙
                         (λ k → comp O A B (q k) (funExt qs k)))
                        j)
                       (λ { (a , b) → qss a b j })))
                   (∘-resp g A (λ a → ΣF (B a) (C a)) t
                    (λ a → graft (B a) (C a) (ts a) (tss a))
                    ∙
                    (λ j →
                       comp O A (λ a → ΣF (B a) (C a)) (q j)
                         λ a →
                           (∘-resp g (B a) (C a) (ts a) (tss a) ∙
                            λ k → comp O (B a) (C a) (qs a k)
                                       λ b → qss a b k) j))
                   i
unique-interpret K O f g p A (set/ .A t₁ t₂ p₁ p₂ i j) =
  isOfHLevel→isOfHLevelDep 2
    (λ a → isSet→isGroupoid (isSetOps O A) (⟪ g ⟫ a) (⟪ interpret K O f ⟫ a))
    _ _
    (cong (unique-interpret K O f g p A) p₁)
    (cong (unique-interpret K O f g p A) p₂)
    (set/ A t₁ t₂ p₁ p₂) i j

open Algebra

FreeAlg-run : {K : FinSetD ℓ₁ → Type ℓ₂} →
              (α : Algebra (FreeOperad K)) →
              run-alg α ≡ interpret _ _ λ A → ⟪ run-alg α ⟫ ∘ Op A
FreeAlg-run α = ⇒≡→≡ _ _ (unique-interpret _ _ _ (run-alg α) λ _ _ → refl)

FreeAlg→ΣΠ : {K : FinSetD ℓ₁ → Type ℓ₂} →
             Algebra (FreeOperad K) →
             Σ[ X ∈ hSet ℓ₁ ] ((A : FinSetD ℓ₁) → K A → (El A → typ X) → typ X)
FreeAlg→ΣΠ alg = Carrier alg , λ A → ⟪ run-alg alg ⟫ ∘ Op A

ΣΠ→FreeAlg : {K : FinSetD ℓ₁ → Type ℓ₂} →
             (X : hSet ℓ₁) → ((A : FinSetD ℓ₁) → K A → (El A → typ X) → typ X) →
             Algebra (FreeOperad K)
Carrier (ΣΠ→FreeAlg X f) = X
run-alg (ΣΠ→FreeAlg X f) = interpret _ _ f

open Iso

FreeAlg↔ΣΠ : (K : FinSetD ℓ₁ → Type ℓ₂) →
             Iso (Algebra (FreeOperad K))
                 (Σ[ X ∈ hSet ℓ₁ ] ((A : FinSetD ℓ₁) → K A → (El A → typ X) → typ X))
fun (FreeAlg↔ΣΠ K)                     = FreeAlg→ΣΠ
inv (FreeAlg↔ΣΠ K)                     = uncurry ΣΠ→FreeAlg
rightInv (FreeAlg↔ΣΠ K) _              = refl
Carrier (leftInv (FreeAlg↔ΣΠ K) alg i) = Carrier alg
run-alg (leftInv (FreeAlg↔ΣΠ K) alg i) = sym (FreeAlg-run alg) i

open import Operad.FinSet

ConFreeAlg : {U : Type ℓ₁} {E : U → Type ℓ₂} {X : Type ℓ₃} →
             Iso ((A : FinSet ℓ₂) (u : U) → E u ≡ ⟦ A ⟧ → (⟦ A ⟧ → X) → X)
                 ((u : U) → isFinite (E u) → (E u → X) → X)
fun      ConFreeAlg f u isFiniteEu g =
  f (_ , isFiniteEu) u refl g
inv      ConFreeAlg f A u p g =
  f u (subst isFinite (sym p) (snd A)) (g ∘ transport p)
rightInv ConFreeAlg f i u isFiniteEu g =
  f u (substRefl {B = isFinite} isFiniteEu i) λ e → cong g (transportRefl e) i
leftInv  ConFreeAlg f i A u p g =
  f (p i , isProp→PathP (λ i → isPropIsFinite {X = p i})
                        (subst isFinite (sym p) (snd A)) (snd A) i)
    u (λ j → p (i ∧ j)) λ x → g (transp (λ j → p (i ∨ j)) i x)

DFConFreeAlg : {U : Type ℓ₁} {E : U → FinSet ℓ₂} {X : Type ℓ₃} →
               Iso ((A : FinSet ℓ₂) (u : U) → E u ≡ A → (⟦ A ⟧ → X) → X)
                   ((u : U) → (⟦ E u ⟧ → X) → X)
fun      (DFConFreeAlg {E = E}) f u g = f (E u) u refl g
inv      DFConFreeAlg f A u p g = f u (g ∘ transport (cong ⟦_⟧ p))
rightInv DFConFreeAlg f i u g = f u λ e → cong g (transportRefl e) i
leftInv  DFConFreeAlg f i A u p g =
  f (p i) u (λ j → p (i ∧ j)) λ x → g (transp (λ j → ⟦ p (i ∨ j) ⟧) i x)
