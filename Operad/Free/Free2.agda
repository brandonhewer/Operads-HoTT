{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Free.Free2 where

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws renaming (assoc to assoc-∙)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (comp)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Cubical.Functions.Embedding

open import Cubical.Data.FinData
open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Unit renaming (Unit to ⊤)
open import Cubical.Data.Sigma hiding (comp)
open import Cubical.Data.Sum

open import Cubical.HITs.PropositionalTruncation renaming (rec to prec)

private
  variable
    ℓ₁ ℓ₂ ℓ₃ ℓ₄ ℓ₅ : Level

  open Iso

  ΣIdLIso : {A : Lift {j = ℓ₂} (Fin 1) → Type ℓ₁} →
            Iso (Σ (Lift (Fin 1)) A) (A (lift zero))
  fun      ΣIdLIso (lift zero , a) = a
  inv      ΣIdLIso a               = lift zero , a
  rightInv ΣIdLIso _               = refl
  leftInv  ΣIdLIso (lift zero , a) = refl

  ΣIdRIso : {A : Type ℓ₁} →
            Iso (Σ A λ _ → Lift {j = ℓ₂} (Fin 1)) A
  fun      ΣIdRIso (a , lift zero) = a
  inv      ΣIdRIso a               = a , lift zero
  rightInv ΣIdRIso _               = refl
  leftInv  ΣIdRIso (a , lift zero) = refl

  ΣAssocIso : {A : Type ℓ₁} {B : A → Type ℓ₂} {C : ∀ a → B a → Type ℓ₃} →
              Iso (Σ (Σ A B) (uncurry C)) (Σ A λ a → Σ (B a) (C a))
  fun      ΣAssocIso ((a , b) , c) = a , b , c
  inv      ΣAssocIso (a , b , c)   = (a , b) , c
  rightInv ΣAssocIso _             = refl
  leftInv  ΣAssocIso _             = refl

  Path-cong-filler : {A : Type ℓ₃} (B : A → Type ℓ₄) {a₁ a₂ : A} →
                     {p q : a₁ ≡ a₂} (b : B a₂) → p ≡ q →
                     PathP (λ i → B (q i)) (subst B (sym p) b) b
  Path-cong-filler B {p = p} b p≡q =
    subst (λ p → PathP (λ i → B (p i)) _ b) p≡q
          λ i → transp (λ j → B (p (i ∨ ~ j))) i b

  lCancel-∙ : {A : Type ℓ₃} {x y z : A}
                  (p : x ≡ y) (q : y ≡ z) →
                  sym p ∙ p ∙ q ≡ q
  lCancel-∙ p q =
    sym p ∙ p ∙ q   ≡⟨ assoc-∙ (sym p) p q ⟩
    (sym p ∙ p) ∙ q ≡⟨ cong (_∙ q) (lCancel p) ⟩
    refl ∙ q        ≡⟨ sym (lUnit q) ⟩
    q               ∎

data isFinite {ℓ : Level} : (A : Type ℓ) → Type (ℓ-suc ℓ) where
  isFiniteT : {A : Type ℓ} → (n : ℕ) → Iso (Fin n) A → isFinite A
  isFinite⊥ : isFinite (Lift (Fin 0))
  isFinite⊤ : isFinite (Lift (Fin 1))
  isFinite⊎ : {A B : Type ℓ} → isFinite A → isFinite B → isFinite (A ⊎ B)
  isFiniteΣ : {A : Type ℓ} {B : A → Type ℓ} →
              isFinite A → (∀ a → isFinite (B a)) → isFinite (Σ A B)
  isPropIsFinite : {A : Type ℓ} → isProp (isFinite A)

FinSetT : ∀ ℓ → Type (ℓ-suc ℓ)
FinSetT ℓ = Σ[ A ∈ Type ℓ ] isFinite A

⟦_⟧ : FinSetT ℓ₁ → Type ℓ₁
⟦_⟧ = fst

isEmbedding⟦⟧ : isEmbedding (⟦_⟧ {ℓ₁})
isEmbedding⟦⟧ _ _ = isEmbeddingFstΣProp λ _ → isPropIsFinite

⟦⟧≡→≡ : {A B : FinSetT ℓ₁} → ⟦ A ⟧ ≡ ⟦ B ⟧ → A ≡ B
⟦⟧≡→≡ = Σ≡Prop λ _ → isPropIsFinite

≡→⟦⟧≡ : {A B : FinSetT ℓ₁} → A ≡ B → ⟦ A ⟧ ≡ ⟦ B ⟧
≡→⟦⟧≡ = cong ⟦_⟧

≡≃⟦⟧≡ : {A B : FinSetT ℓ₁} → (⟦ A ⟧ ≡ ⟦ B ⟧) ≃ (A ≡ B)
≡≃⟦⟧≡ = Σ≡PropEquiv λ _ → isPropIsFinite

≡→⟦⟧≡-inj : {A B : FinSetT ℓ₁} {p q : A ≡ B} →
            ≡→⟦⟧≡ p ≡ ≡→⟦⟧≡ q → p ≡ q
≡→⟦⟧≡-inj {A = A} {B} {p = p} {q} p≡q =
  fst (fst (equiv-proof (isEquiv→isEmbedding (isEmbedding⟦⟧ A B) p q) p≡q))

_⊎F_ : (A B : FinSetT ℓ₁) → FinSetT ℓ₁
(A , p) ⊎F (B , q) = A ⊎ B , isFinite⊎ p q

ΣF : (A : FinSetT ℓ₁) → (⟦ A ⟧ → FinSetT ℓ₁) → FinSetT _
ΣF A B = (Σ ⟦ A ⟧ (⟦_⟧ ∘ B)) , isFiniteΣ (snd A) (snd ∘ B)

⊥F : FinSetT ℓ₁
⊥F = _ , isFinite⊥

⊤F : FinSetT ℓ₁
⊤F = _ , isFinite⊤

FinT : ℕ → FinSetT ℓ₁
FinT n = Lift (Fin n) , isFiniteT n LiftIso

ΣIdL : (A : Lift (Fin 1) → FinSetT ℓ₁) → ΣF ⊤F A ≡ A (lift zero)
ΣIdL _ = ⟦⟧≡→≡ (isoToPath ΣIdLIso)

ΣIdR : (A : FinSetT ℓ₁) → ΣF A (λ _ → ⊤F) ≡ A
ΣIdR _ = ⟦⟧≡→≡ (isoToPath ΣIdRIso)

ΣAssoc : (A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁)
         (C : ∀ a → ⟦ B a ⟧ → FinSetT ℓ₁) →
         ΣF (ΣF A B) (uncurry C) ≡ ΣF A λ a → ΣF (B a) (C a)
ΣAssoc A B C = ⟦⟧≡→≡ (isoToPath ΣAssocIso)

ΣIdl≡ΣIdR-⊤ : ΣIdL (λ _ → ⊤F {ℓ₁}) ≡ ΣIdR ⊤F
ΣIdl≡ΣIdR-⊤ {ℓ₁} =
  cong ⟦⟧≡→≡ (
    isInjectiveTransport (funExt λ { (lift zero , lift zero) → refl })
  )

FinSet-transport-inj : {A B : FinSetT ℓ₁} {p q : A ≡ B} →
                       transport (≡→⟦⟧≡ p) ≡ transport (≡→⟦⟧≡ q) → p ≡ q
FinSet-transport-inj p = ≡→⟦⟧≡-inj (isInjectiveTransport p)                       

transport-distr : {A B C : Type ℓ₁} (p : A ≡ B) (q : B ≡ C) →
                  transport (p ∙ q) ≡ transport q ∘ transport p
transport-distr {A = A} p q =
  funExt λ a i →
    transp (λ j → q j) i0
      (transp (λ j → p j) i0
        (transp (λ _ → A) i a))

module _ {A B : FinSetT ℓ₁} where

  ≃-FinSet≡ : (p q : A ≡ B) →
              pathToEquiv (cong ⟦_⟧ p) .fst ≡ pathToEquiv (cong ⟦_⟧ q) .fst →
              p ≡ q
  ≃-FinSet≡ p q r =
    equiv-proof (isEquiv→isEmbedding (isEmbeddingFstΣProp λ _ → isPropIsFinite) p q)
                (invEq (congEquiv univalence) (Σ≡Prop isPropIsEquiv r))
                .fst .fst

ΣIdr-ΣAssoc-lem : (A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁) →
                  cong (ΣF A) (funExt (sym ∘ ΣIdR ∘ B)) ≡
                  sym (ΣIdR (ΣF A B)) ∙ ΣAssoc A B (λ _ _ → ⊤F)
ΣIdr-ΣAssoc-lem {ℓ₁} A B =
  ≃-FinSet≡ _ _ (funExt λ x → q x ∙ p x)
  where
    p : ∀ x → (fst x , snd x , lift zero) ≡
              pathToEquiv (cong ⟦_⟧ (sym (ΣIdR (ΣF A B)) ∙
                                     ΣAssoc A B λ _ _ → ⊤F)) .fst x
    p (a , b) i =
      transp (λ _ → Σ ⟦ A ⟧ λ a → Σ ⟦ B a ⟧ λ _ → Lift {j = ℓ₁} (Fin 1)) (~ i)
        (transp (λ _ → ⟦ A ⟧) (~ i) (transp (λ _ → ⟦ A ⟧) (~ i) a) ,
         transp (λ j → ⟦ B (transp (λ _ → ⟦ A ⟧) (~ i ∨ ~ j)
                             (transp (λ _ → ⟦ A ⟧) (~ i) a)) ⟧) (~ i)
           (transp (λ j → ⟦ B (transp (λ _ → ⟦ A ⟧) (~ i ∨ ~ j) a) ⟧) (~ i) b) ,
         lift zero)

    q : ∀ x → pathToEquiv (cong ⟦_⟧ (cong (ΣF A) (funExt (sym ∘ ΣIdR ∘ B)))) .fst x ≡
              (fst x , snd x , lift zero)
    q (a , b) i =
      transp (λ _ → ⟦ A ⟧) i a ,
      transp (λ j → ⟦ B (transp (λ _ → ⟦ A ⟧) (i ∨ ~ j) a) ⟧)
             i (equivFun (idEquiv ⟦ B a ⟧) b) ,
      lift zero

ΣAssoc-ΣIdr-lem : 
  (A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁) →
  cong (ΣF A) (funExt (ΣIdR ∘ B)) ≡
  sym (ΣAssoc A B (λ _ _ → ⊤F)) ∙ ΣIdR (ΣF A B)
ΣAssoc-ΣIdr-lem A B =
  cong sym (
    ΣIdr-ΣAssoc-lem A B ∙
    sym (symDistr (sym (ΣAssoc A B (λ _ _ → ⊤F))) (ΣIdR (ΣF A B)))
  )

module _ (K : FinSetT ℓ₁ → Type ℓ₂) where

  data Free : FinSetT ℓ₁ → Type (ℓ-max (ℓ-suc ℓ₁) ℓ₂) where
    leaf : Free ⊤F
    corolla : (A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁) →
              K A → (∀ a → Free (B a)) → Free (ΣF A B)
    set/ : ∀ {A} → isSet (Free A)

  recFree : (F : FinSetT ℓ₁ → Type ℓ₃) →
            (∀ A → isSet (F A)) → F ⊤F →
            ((A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁) →
             K A → (∀ a → F (B a)) → F (ΣF A B)) →
            ∀ {A} → Free A → F A
  recFree F isSetF Fl Fc leaf = Fl
  recFree F isSetF Fl Fc (corolla A B k ts) = Fc A B k (recFree F isSetF Fl Fc ∘ ts)
  recFree F isSetF Fl Fc (set/ t u p q i j) =
    isSetF _ (recFree F isSetF Fl Fc t)
             (recFree F isSetF Fl Fc u)
             (cong (recFree F isSetF Fl Fc) p)
             (cong (recFree F isSetF Fl Fc) q) i j

  elimFree : (F : (A : FinSetT ℓ₁) → Free A → Type ℓ₃) →
             F ⊤F leaf →
             ((A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁) (k : K A)
              (ts : ∀ a → Free (B a)) → (∀ a → F (B a) (ts a)) →
              F (ΣF A B) (corolla A B k ts)) →
             (∀ A (t : Free A) → isSet (F A t)) →
             ∀ {A} (t : Free A) → F A t
  elimFree F Fl Fc isSetF leaf = Fl
  elimFree F Fl Fc isSetF (corolla A B k ts) = Fc A B k ts (elimFree F Fl Fc isSetF ∘ ts)
  elimFree F Fl Fc isSetF {A} (set/ t u p q i j)  =
    isSet→SquareP (λ i j → isSetF A (set/ t u p q i j))
                  (λ i → elimFree F Fl Fc isSetF (p i))
                  (λ i → elimFree F Fl Fc isSetF (q i))
                  (λ _ → elimFree F Fl Fc isSetF t)
                  (λ _ → elimFree F Fl Fc isSetF u) i j

  graft : (A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁) →
          Free A → (∀ a → Free (B a)) → Free (ΣF A B)
  graft _ B leaf ts = subst Free (sym (ΣIdL _)) (ts (lift zero))
  graft _ B (corolla A C t ts) tss =
    subst Free (sym (ΣAssoc _ _ _)) (corolla A _ t λ a → graft _ _ (ts a) (tss ∘ (a ,_)))
  graft _ B (set/ t u p q i j) tss =
    set/ (graft _ B t tss)
         (graft _ B u tss)
         (λ i → graft _ B (p i) tss)
         (λ i → graft _ B (q i) tss) i j

  graft-subst₂ : {A : FinSetT ℓ₁} {B₁ B₂ : ⟦ A ⟧ → FinSetT ℓ₁} (p : B₁ ≡ B₂)
                 (t : Free A) (ts : ∀ a → Free (B₁ a)) →
                 subst Free (cong (ΣF A) p) (graft A B₁ t ts) ≡
                 graft A B₂ t ((λ {a} → subst Free (λ i → p i a)) ∘ ts)
  graft-subst₂ {A} {B₁} =
    J (λ B₂ p →
         (t : Free A) (ts : ∀ a → Free (B₁ a)) →
         subst Free (cong (ΣF A) p) (graft A B₁ t ts) ≡
         graft A B₂ t ((λ {a} → subst Free (λ i → p i a)) ∘ ts)
      )
      (λ t ts →
         substRefl {B = Free} (graft A B₁ t ts) ∙
         cong (graft A B₁ t) (funExt (sym ∘ substRefl {B = Free} ∘ ts))
      )

  graft-subst : {A₁ A₂ : FinSetT ℓ₁} (p : A₁ ≡ A₂)
                (B₁ : ⟦ A₁ ⟧ → FinSetT ℓ₁) (B₂ : ⟦ A₂ ⟧ → FinSetT ℓ₁)
                (q : PathP (λ i → ⟦ p i ⟧ → FinSetT ℓ₁) B₁ B₂)
                (t : Free A₁) (ts : ∀ a → Free (B₁ a)) →
                subst Free (cong₂ ΣF p q) (graft A₁ B₁ t ts) ≡
                graft A₂ B₂ (subst Free p t)
                            ((λ {a} → subst Free λ i → q i (transp (λ j → ⟦ p (i ∨ ~ j) ⟧) i a)) ∘
                             ts ∘ subst⁻ ⟦_⟧ p)
  graft-subst {A₁} =
    J (λ A₂ p →
         (B₁ : ⟦ A₁ ⟧ → FinSetT ℓ₁) (B₂ : ⟦ A₂ ⟧ → FinSetT ℓ₁)
         (q : PathP (λ i → ⟦ p i ⟧ → FinSetT ℓ₁) B₁ B₂)
         (t : Free A₁) (ts : ∀ a → Free (B₁ a)) →
         subst Free (cong₂ ΣF p q) (graft A₁ B₁ t ts) ≡
         graft A₂ B₂ (subst Free p t)
                              ((λ {a} → subst Free λ i → q i (transp (λ j → ⟦ p (i ∨ ~ j) ⟧) i a)) ∘
                               ts ∘ subst⁻ ⟦_⟧ p)
      )
      (λ B₁ B₂ q t ts →
         graft-subst₂ q t ts ∙
         (λ i → graft A₁ B₂ (transp (λ _ → Free A₁) (~ i) t)
                  λ a → subst Free (λ j → q j (transp (λ _ → ⟦ A₁ ⟧) (~ i ∨ j) a))
                                   (ts (transp (λ _ → ⟦ A₁ ⟧) (~ i) a)))
      )
  
  graft-subst₁ : {A₁ A₂ : FinSetT ℓ₁} (p : A₁ ≡ A₂) (B : ⟦ A₂ ⟧ → FinSetT ℓ₁) →
                 (t : Free A₁) (ts : ∀ a → Free (B a)) →
                 subst Free (cong₂ ΣF p λ i a → B (transp (λ j → ⟦ p (i ∨ j) ⟧) i a))
                            (graft A₁ (B ∘ subst ⟦_⟧ p) t (ts ∘ subst ⟦_⟧ p)) ≡
                 graft A₂ B (subst Free p t) ts
  graft-subst₁ {A₂ = A₂} p B t ts =
    graft-subst p (B ∘ subst ⟦_⟧ p) B (λ i a → B (transp (λ j → ⟦ p (i ∨ j) ⟧) i a))
                t (ts ∘ subst ⟦_⟧ p) ∙
    cong (graft A₂ B (subst Free p t))
         (funExt λ a i →
           transp (λ j → Free (B (transp (λ k → ⟦ p (i ∨ j ∨ k) ⟧) (i ∨ j)
                                         (transp (λ k → ⟦ p (i ∨ j ∨ ~ k) ⟧) (i ∨ j) a)))) i
                  (ts (transp (λ j → ⟦ p (i ∨ j) ⟧) i
                              (transp (λ j → ⟦ p (i ∨ ~ j) ⟧) i a)))
         )

  fidl : ∀ A t → PathP (λ i → Free (ΣIdL A i))
                       (graft ⊤F A leaf t) (t (lift zero))
  fidl A t i = transp (λ j → Free (ΣIdL A (i ∨ ~ j))) i (t (lift zero))

  fidr : ∀ A t → PathP (λ i → Free (ΣIdR A i))
                       (graft A (λ _ → ⊤F) t λ _ → leaf) t
  fidr _ (set/ t u p q i j) k =
    set/ (fidr _ t k)
         (fidr _ u k)
         (λ i → fidr _ (p i) k)
         (λ i → fidr _ (q i) k) i j
  fidr _ leaf =
    Path-cong-filler Free leaf ΣIdl≡ΣIdR-⊤
  fidr _ (corolla A B k ts) =
    toPathP (sym (substComposite Free _ _ (corolla A _ _ _)) ∙
            (λ i →
                 subst Free (ΣAssoc-ΣIdr-lem A B (~ i))
                       (corolla _ _ k λ a →
                        fromPathP (symP (fidr (B a) (ts a))) (~ i)
                       )
            ) ∙
            cong (subst Free _) q ∙
            sym (substComposite Free _ _ (corolla A B k ts)) ∙
            (λ i →
                 subst Free (
                   ΣIdr-ΣAssoc-lem A B (~ i) ∙ cong (ΣF A) (funExt (ΣIdR ∘ B))
                 ) (corolla A B k ts)
            ) ∙
            cong (λ p → subst Free p (corolla A B k ts)) (lCancel _) ∙
            substRefl {B = Free} (corolla A B k ts))
    where
      u : (λ a → subst Free (sym (ΣIdR (B a))) (ts a)) ≡
          subst (λ B → (a : ⟦ A ⟧) → Free (B a))
                (funExt (λ a → sym (ΣIdR (B a)))) ts
      u = funExt (λ a i →
           transp (λ j →
             Free (ΣIdR (B (transp (λ _ → ⟦ A ⟧) (~ i ∨ j) a)) (~ j))
           ) i0 (ts (transp (λ _ → ⟦ A ⟧) (~ i) a))
          )

      q : corolla A (λ a → ΣF (B a) (λ _ → ⊤F)) k
                    (λ a → subst Free (sym (ΣIdR (B a))) (ts a))
          ≡ subst Free (sym (ΣIdR _) ∙ ΣAssoc A B λ _ _ → ⊤F) (corolla A B k ts)
      q = cong {B = λ _ → Free (ΣF A λ a → ΣF (B a) λ _ → ⊤F)}
               (corolla A (λ a → ΣF (B a) (λ _ → ⊤F)) k) u ∙
          sym (substCommSlice (λ B → (a : ⟦ A ⟧) → Free (B a))
                              (λ B → Free _)
                              (λ B ts → corolla A B k ts)
                              (funExt (sym ∘ ΣIdR ∘ B)) ts) ∙
          cong (λ q → subst Free q (corolla A B k ts))
               (ΣIdr-ΣAssoc-lem _ _)

  fassoc : ∀ A B C t ts tss →
             PathP (λ i → Free (ΣAssoc A B C i))
                   (graft (ΣF A B) (uncurry C) (graft A B t ts) (uncurry tss))
                   (graft A (λ a → ΣF (B a) (C a)) t λ a → graft (B a) (C a) (ts a) (tss a))
  fassoc A B C (set/ t u p q i j) ts tss k =
    set/ (fassoc A B C t ts tss k)
         (fassoc A B C u ts tss k)
         (λ i → fassoc A B C (p i) ts tss k)
         (λ i → fassoc A B C (q i) ts tss k) i j
  fassoc _ B C leaf ts tss = {!!}
  fassoc _ B C (corolla A D k t) ts tss = {!!}

  open import Operad.Base
    FinSetT ⟦_⟧ ⊤F (lift zero) ΣF ΣIdL
    ΣIdR uncurry (λ _ → uncurry) ΣAssoc

  open import Operad.Morphism
    FinSetT ⟦_⟧ ⊤F (lift zero) ΣF ΣIdL
    ΣIdR uncurry (λ _ → uncurry) ΣAssoc

  open Operad

  FreeOperad : Operad _ _
  Ops FreeOperad = Free
  isSetOps FreeOperad _ = set/
  id FreeOperad = leaf
  comp FreeOperad = graft
  idl FreeOperad = fidl
  idr FreeOperad = fidr
  assoc FreeOperad = fassoc


  ηF : ∀ A → K A → Free A
  ηF A k = subst Free (ΣIdR A) (corolla _ _ k λ _ → leaf)

  {-

  graft _ B (corolla A C t ts) tss =
    subst Free (sym (ΣAssoc _ _ _)) (corolla A _ t λ a → graft _ _ (ts a) (tss ∘ (a ,_)))

  subst Free
    (cong₂ ΣF (ΣIdR A) (λ i a → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a)))
    (subst Free (sym (ΣAssoc _ _ _))
                (corolla A _ k λ a → graft _ _ leaf (ts ∘ subst ⟦_⟧ (ΣIdR A) ∘ (a ,_))))
    ≡ corolla A B k ts


   subst Free
    (cong₂ ΣF (ΣIdR A) (λ i a → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a)))
    (subst Free (sym (ΣAssoc _ _ _))
                (corolla A _ k λ a → subst Free (sym (ΣIdL _)) (ts (transp (λ _ → ⟦ A ⟧) i0 a))))
    ≡ corolla A B k ts

   subst Free
    (sym (ΣAssoc _ _ _) ∙ cong₂ ΣF (ΣIdR A) (λ i a → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a)))
    (corolla A _ k λ a → subst Free (sym (ΣIdL _)) (ts (transp (λ _ → ⟦ A ⟧) i0 a)))
   ≡ corolla A B k ts

   --  λ a → subst Free (ΣIdL _) (ts (subst ⟦_⟧ (ΣIdR A) (a , lift zero)))
  -}

  -- graft A B (subst Free (ΣIdR A) (corolla _ _ k λ _ → leaf)) ts ≡ corolla A B k ts
  η-unit : ∀ A B k ts → graft A B (ηF A k) ts ≡ corolla A B k ts
  η-unit A B k ts =
    sym (graft-subst₁ (ΣIdR A) B (corolla _ _ k λ _ → leaf) ts) ∙
    (λ i →
      subst Free
        (cong₂ ΣF (ΣIdR A) (λ i a → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a)))
        (subst Free (sym (ΣAssoc _ _ _))
               (corolla A _ k λ a →
                  fromPathP (symP (fidl _ (ts ∘ subst ⟦_⟧ (ΣIdR A) ∘ (a ,_)))) i))
    ) ∙
    sym (substComposite Free (sym (ΣAssoc _ _ _))
                             (cong₂ ΣF (ΣIdR A) (λ i a → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a)))
                             (corolla A _ k λ a →
                               subst Free (sym (ΣIdL _)) (ts (transp (λ _ → ⟦ A ⟧) i0 a)))) ∙
    {!!}
    where
      q : ΣF A (λ a → ΣF ⊤F λ z → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (a , z))) ≡
          ΣF (ΣF A (λ _ → ⊤F)) (λ a → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 a))
      q =
        cong₂ ΣF (sym (ΣIdR A)) λ i a →
          transp {!λ j → ?!} {!!} {!!}

      {-
      PathP (λ i → ⟦ ΣIdR A (~ i) ⟧ → FinSetT ℓ₁)
    (λ z → ΣF ⊤F (λ z₁ → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (z , z₁))))
    (λ z → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 z)
       -}

      t : ΣF A (λ a → ΣF ⊤F λ z → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (a , z))) ≡ ΣF A B
      t = sym (ΣAssoc _ _ _) ∙ cong₂ ΣF (ΣIdR A) (λ i a → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a))

      u : ΣF A (λ a → ΣF ⊤F λ z → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (a , z))) ≡ ΣF A B
      u = cong (ΣF A) (funExt λ a → 
            ΣIdL (λ z → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (a , z))) ∙
            cong B (λ i →
              fst
              (equivProof ⟦ A ⟧ ⟦ A ⟧ (idEquiv ⟦ A ⟧)
              (transp (λ i → ⟦ A ⟧) i
              (equivFun (isoToEquiv (ΣIdRIso {ℓ₂ = ℓ₂})) (a , lift zero)))
              i0
              (λ .o → _
              ,
              (λ _ →
              transp (λ i → ⟦ A ⟧) i
              (equivFun (isoToEquiv (ΣIdRIso {ℓ₂ = ℓ₂})) (a , lift zero)))))
              )
          )

      lem : t ≡ u
      lem i = {!!}
      -- subst Free (transportRefl A)

      -- ΣF A (λ a → ΣF ⊤F λ _ → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a))

      {-lem : (a : ⟦ A ⟧) →
            (corolla A _ k λ a →
               subst Free (sym (ΣIdL λ _ → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (a , lift zero))))
                          (ts (transp (λ _ → ⟦ A ⟧) i0 a))) ≡
             subst Free (cong (ΣF A) λ i a → B (transp (λ j → ⟦ ΣIdR A (i ∨ j) ⟧) i a))
                        (corolla A _ k ts)
      lem a = {!!}-}

 {-
      lem′ : (A : FinSetT ℓ₁) (B : ⟦ A ⟧ → FinSetT ℓ₁)
             (ts : ∀ a → Free (B a)) (a : ⟦ A ⟧) →
             subst Free (sym (ΣIdL λ _ → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (a , lift zero))))
                         (ts ((transp (λ _ → ⟦ A ⟧) i0 a))) ≡
             subst Free (cong B {!!} ∙
                         sym (ΣIdL λ _ → B (transp (λ j → ⟦ ΣIdR A j ⟧) i0 (a , lift zero))))
                        (ts a)
      lem′ A B ts a =
        let q = lem A B ts a
         in {!f!}-}

   -- F (transport refl A)

    -- transport ⟦
    {-
    sym (graft-corolla′ A B k ts) ∙
    graft-subst₂ (funExt (λ a → ΣIdL λ _ → B a))
                 (subst Free (ΣIdR A) (corolla _ _ k λ _ → leaf))
                 ((λ {a} → subst Free (sym (ΣIdL (λ _ → B a)))) ∘ ts) ∙
    cong (graft A B (ηF A k))
      (funExt λ a →
        sym (substComposite Free (sym (ΣIdL λ _ → B a)) (ΣIdL λ _ → B a) (ts a)) ∙
        cong (λ p → subst Free p (ts a)) (lCancel (ΣIdL λ _ → B a))  ∙
        substRefl {B = Free} (ts a)
      )-}

  open _⇒ᵒᵖ_

  interpret : (O : Operad ℓ₁ ℓ₃) →
              (f : ∀ A → K A → Ops O A) →
              ∀ {A} → Free A → Ops O A
  interpret O f leaf = id O
  interpret O f (corolla A B k ts) =
    comp O _ _ (f A k) (interpret O f ∘ ts)
  interpret O f (set/ t u p q i j) =
    isSetOps O _ (interpret O f t)
                 (interpret O f u)
                 (λ i → interpret O f (p i))
                 (λ i → interpret O f (q i)) i j

  interpret-∘ : (O : Operad ℓ₁ _)
                (f : ∀ A → K A → Ops O A)
                (A : FinSetT ℓ₁) (t : Free A)
                (B : ⟦ A ⟧ → FinSetT ℓ₁) (ts : ∀ a → Free (B a)) →
                interpret O f (graft A B t ts) ≡
                comp O A B (interpret O f t) (interpret O f ∘ ts)
  interpret-∘ O f A t =
    elimFree (λ A t → (B : ⟦ A ⟧ → FinSetT ℓ₁) (ts : ∀ a → Free (B a)) →
                      interpret O f (graft A B t ts) ≡
                      comp O A B (interpret O f t) (interpret O f ∘ ts))
             (λ B ts →
              sym (substCommSlice Free (Ops O)
                   (λ _ → interpret O f) (sym (ΣIdL B)) (ts (lift zero))) ∙
              fromPathP (symP (idl O B (interpret O f ∘ ts)))
             )
             (λ A B k ts ih C tss →
              sym (substCommSlice Free (Ops O)
                   (λ _ → interpret O f) (sym (ΣAssoc A _ _))
                   (corolla _ _ k λ a → graft _ _ (ts a) (tss ∘ (a ,_)))) ∙
              cong (λ x → subst (Ops O) (sym (ΣAssoc _ _ _))
                            (comp O A _ (f A k) x))
                   (funExt (λ a → ih a _ _)) ∙
              fromPathP (symP (assoc O A _ _ (f A k) _ _))
             )
             (λ A t → isSetΠ2 λ B ts → isProp→isSet (isSetOps O _ _ _)) t

  interpretOp : (O : Operad ℓ₁ _) →
                (f : ∀ A → K A → Ops O A) →
                FreeOperad ⇒ᵒᵖ O
  ⟪ interpretOp O f ⟫ = interpret O f
  id-resp (interpretOp O f) = refl
  ∘-resp (interpretOp O f) A B t ts = interpret-∘ O f A t B ts

  interpret-η : (O : Operad ℓ₁ _) →
                (f : ∀ A → K A → Ops O A) →
                ∀ {A} k → interpret O f (ηF A k) ≡ f A k
  interpret-η O f {A} k =
    sym (substCommSlice Free (Ops O)
         (λ _ → interpret O f) (ΣIdR A)
         (corolla _ _ k λ _ → leaf)) ∙
    fromPathP (idr O A (f A k))

  unique-interpret : (O : Operad ℓ₁ ℓ₃) →
                     (f : ∀ A → K A → Ops O A) →
                     (g : FreeOperad ⇒ᵒᵖ O) →
                     (∀ {A} k → ⟪ g ⟫ (ηF A k) ≡ f A k) →
                     ∀ {A} (t : Free A) → ⟪ g ⟫ t ≡ interpret O f t
  unique-interpret O f g g-η =
    elimFree (λ _ t → ⟪ g ⟫ t ≡ interpret O f t)
             (id-resp g)
             (λ A B k ts ih →
                cong ⟪ g ⟫ (sym (η-unit A B k ts)) ∙
                ∘-resp g A B (ηF A k) ts ∙
                (λ i → comp O A B (g-η k i) λ a → ih a i)
             )
             (λ _ _ → isProp→isSet (isSetOps O _ _ _))

open import Operad.Base
  FinSetT ⟦_⟧ ⊤F (lift zero) ΣF ΣIdL
  ΣIdR uncurry (λ _ → uncurry) ΣAssoc

open import Operad.Morphism
  FinSetT ⟦_⟧ ⊤F (lift zero) ΣF ΣIdL
  ΣIdR uncurry (λ _ → uncurry) ΣAssoc

open Operad

record OpMonad (O : Operad ℓ₁ ℓ₂) (X : Type ℓ₃) : Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-max ℓ₂ ℓ₃)) where
  field
    Idx : FinSetT ℓ₁
    Op : Ops O Idx
    Data : ⟦ Idx ⟧ → X

open OpMonad

OpMonad-∘ : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} →
            OpMonad O (OpMonad O X) → OpMonad O X
Idx  (OpMonad-∘ x)         = ΣF (Idx x) (Idx ∘ Data x)
Op   (OpMonad-∘ {O = O} x) = comp O _ _ (Op x) (Op ∘ Data x)
Data (OpMonad-∘ x) (i , j) = Data (Data x i) j

OpMonad-η : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} → X → OpMonad O X
Idx  (OpMonad-η x)         = ⊤F
Op   (OpMonad-η {O = O} x) = id O
Data (OpMonad-η x) _       = x

return : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} → X → OpMonad O X
return = OpMonad-η

OpMonad-map : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} {Y : Type ℓ₄} →
              (X → Y) → OpMonad O X → OpMonad O Y
Idx  (OpMonad-map f x)   = Idx x
Op   (OpMonad-map f x)   = Op x
Data (OpMonad-map f x) i = f (Data x i)

fmap : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} {Y : Type ℓ₄} →
       (X → Y) → OpMonad O X → OpMonad O Y
fmap = OpMonad-map

OpMonad-bind : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} {Y : Type ℓ₄} →
               OpMonad O X → (X → OpMonad O Y) → OpMonad O Y
Idx  (OpMonad-bind x f)         = ΣF (Idx x) (Idx ∘ f ∘ Data x)
Op   (OpMonad-bind {O = O} x f) = comp O _ _ (Op x) (Op ∘ f ∘ Data x)
Data (OpMonad-bind x f) (i , j) = Data (f (Data x i)) j

_>>=_ : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} {Y : Type ℓ₄} →
        OpMonad O X → (X → OpMonad O Y) → OpMonad O Y
_>>=_ = OpMonad-bind

_<*>_ : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} {Y : Type ℓ₄} →
        OpMonad O (X → Y) → OpMonad O X → OpMonad O Y
of <*> ox = of >>= λ f → ox >>= λ x → return (f x)

liftO2 : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} {Y : Type ℓ₄} {Z : Type ℓ₅} →
         (X → Y → Z) → OpMonad O X → OpMonad O Y → OpMonad O Z
liftO2 f ox oy = ox >>= λ x → oy >>= λ y → return (f x y)

liftFreeOp : (K : FinSetT ℓ₁ → Type ℓ₂) {X : Type ℓ₃} →
             ∀ {A} → K A → (⟦ A ⟧ → OpMonad (FreeOperad K) X) → OpMonad (FreeOperad K) X
Idx  (liftFreeOp K {A = A} k xs) = ΣF A (Idx ∘ xs)
Op   (liftFreeOp K k xs)         = comp (FreeOperad K) _ _ (ηF K _ k) (Op ∘ xs)
Data (liftFreeOp K k xs) (i , j) = Data (xs i) j

syntax liftFreeOp K k f = K [ k ↑ f ]

OpMonad-comp : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} {Y : Type ℓ₄} {Z : Type ℓ₅} →
               (x : OpMonad O X) →
               (⟦ Idx x ⟧ → OpMonad O Y) →
               (X → Y → Z) → OpMonad O Z
Idx  (OpMonad-comp x f α)         = ΣF (Idx x) (Idx ∘ f)
Op   (OpMonad-comp {O = O} x f α) = comp O _ _ (Op x) (Op ∘ f)
Data (OpMonad-comp x f α) (i , j) = α (Data x i) (Data (f i) j)

OpMonad-run : {O : Operad ℓ₁ ℓ₂} {X : Type ℓ₃} →
              (∀ A → Ops O A → (⟦ A ⟧ → X) → X) →
              OpMonad O X → X
OpMonad-run f x = f (Idx x) (Op x) (Data x)

OpMonad-runFree :
  (K : FinSetT ℓ₁ → Type ℓ₂) {X : Type ℓ₃} →
  isSet X → (∀ {A} → K A → (⟦ A ⟧ → X) → X) →
  OpMonad (FreeOperad K) X → X
OpMonad-runFree K {X} isSetX f =
  OpMonad-run ffun
  where
    ffun : ∀ A → Free K A → (⟦ A ⟧ → X) → X
    ffun _ k =
      recFree K (λ A → (⟦ A ⟧ → X) → X)
              (λ _ → isSetΠ λ _ → isSetX)
              (λ f → f (lift zero))
              (λ _ _ k xs₁ xs₂ → f k (λ a → xs₁ a (xs₂ ∘ (a ,_)))) k

data ℕOps : FinSetT ℓ-zero → Type₁ where
  constN    : (n : ℕ) → ℕOps ⊥F
  succ      : ℕOps (FinT 1)
  plus mult : ℕOps (FinT 2)

ℕOpM : (A : Type ℓ₁) → Type _
ℕOpM = OpMonad (FreeOperad ℕOps)

liftℕ2 : {A : Type ℓ₁} → ℕOps (FinT 2) → ℕOpM A → ℕOpM A → ℕOpM A
liftℕ2 o x y = ℕOps [ o ↑ (λ { (lift zero) → x; (lift (suc _)) → y }) ]

constM : {A : Type ℓ₁} → ℕ → ℕOpM A
constM n = ℕOps [ constN n ↑ (λ ()) ]

succM : {A : Type ℓ₁} → ℕOpM A → ℕOpM A
succM x = ℕOps [ succ ↑ (λ _ → x) ]

_+M_ : {A : Type ℓ₁} → ℕOpM A → ℕOpM A → ℕOpM A
_+M_ = liftℕ2 plus

_*M_ : {A : Type ℓ₁} → ℕOpM A → ℕOpM A → ℕOpM A
_*M_ = liftℕ2 mult

intℕOps : ∀ {A} → ℕOps A → (⟦ A ⟧ → ℕ) → ℕ
intℕOps (constN n) xs = n
intℕOps succ       xs = xs (lift zero)
intℕOps plus       xs = xs (lift zero) + xs (lift (suc zero))
intℕOps mult       xs = xs (lift zero) * xs (lift (suc zero))

eval : ℕOpM ℕ → ℕ
eval = OpMonad-runFree ℕOps isSetℕ intℕOps

ex : {A : Type ℓ₁} → ℕOpM ℕ → ℕOpM ℕ → ℕOpM ℕ
ex x y = OpMonad-comp (x +M y) (return ∘ exFun) λ x f → f x
  where
    exFun : ⟦ Idx (x +M y) ⟧ → ℕ → ℕ
    exFun (lift zero , _)    = 2 +_
    exFun (lift (suc _) , _) = 3 *_

z : ℕOpM ℕ
z = return 0

one : ℕOpM ℕ
one = return 1

ten : ℕOpM ℕ
ten = return 10

twentyM : ℕOpM ℕ
twentyM = ten +M ten

-- (x y : ℕOpM a) → (idx (x +M y) → ℕOpM b) → (a → b → c) → m c


-- (x : m a) → (idx x → m b) → (a → b → c) → m c

-- 
