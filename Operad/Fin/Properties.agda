{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Fin.Properties where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.Fin as Fin hiding (discreteFin; isSetFin; isContrFin1; any?; punchOut; toℕ)
                                    renaming (Fin to Fin′; ¬Fin0 to ¬Fin′0; Fin-inj to Fin-inj′′)
open import Cubical.Data.FinData
open import Cubical.Data.Nat hiding (znots; snotz)
                             renaming (_·_ to _*_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Transport

open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection

open import Cubical.HITs.PropositionalTruncation hiding (map) renaming (rec to p-rec)

open import Cubical.Relation.Nullary

open import Operad.Fin.Base
open import Operad.Sum as Sum

private

  <ℕ→Fin : ∀ n → Fin′ n → Fin n
  <ℕ→Fin zero    i           = ⊥-rec (¬Fin′0 i)
  <ℕ→Fin (suc n) (zero  , p) = zero
  <ℕ→Fin (suc n) (suc i , p) = suc (<ℕ→Fin n (i , pred-≤-pred p))

  Fin→<ℕ : ∀ n → Fin n → Fin′ n
  Fin→<ℕ (suc n) zero    = fzero
  Fin→<ℕ (suc n) (suc i) = fsuc (Fin→<ℕ n i)

  →fsuc : ∀ m k → (p : suc k < suc m) → fsuc (k , pred-≤-pred p) ≡ (suc k , p)
  →fsuc m k p = ΣPathP (refl , m≤n-isProp (snd (fsuc (k , pred-≤-pred p))) p)

  <ℕ→Fin→<ℕ : ∀ n i → Fin→<ℕ n (<ℕ→Fin n i) ≡ i
  <ℕ→Fin→<ℕ zero    i           = ⊥-rec (¬Fin′0 i)
  <ℕ→Fin→<ℕ (suc n) (zero  , p) = ΣPathP (refl , m≤n-isProp (snd fzero) p)
  <ℕ→Fin→<ℕ (suc n) (suc i , p) = cong fsuc (<ℕ→Fin→<ℕ n (i , pred-≤-pred p)) ∙ →fsuc n i p

  pred-fsuc : ∀ {n} (i : Fin′ n) → snd i ≡ pred-≤-pred (snd (fsuc i))
  pred-fsuc i = m≤n-isProp (snd i) (pred-≤-pred (snd (fsuc i)))

  inject+0 : ∀ {m} n → (i : Fin (suc m)) → i ≡ zero → inject+ {suc m} n i ≡ zero
  inject+0 n zero    p = refl
  inject+0 n (suc i) p = ⊥-rec (snotz p)

  Fin→<ℕ→Fin : ∀ n i → <ℕ→Fin n (Fin→<ℕ n i) ≡ i
  Fin→<ℕ→Fin (suc n) zero    = refl
  Fin→<ℕ→Fin (suc n) (suc i) =
    cong Fin.suc (
      sym (
        cong (<ℕ→Fin n) (
          ΣPathP (refl , pred-fsuc (Fin→<ℕ n i))
        )
      ) ∙ Fin→<ℕ→Fin n i
    )

  ΣFin→⊎Fin : ∀ n ns → Σ[ i ∈ Fin n ] Fin (ns i) → ⊎Fin n ns
  ΣFin→⊎Fin (suc n) ns (zero  , j) = inl j
  ΣFin→⊎Fin (suc n) ns (suc i , j) = inr (ΣFin→⊎Fin n (ns ∘ suc) (i , j))

  ⊎Fin→ΣFin : ∀ n ns → ⊎Fin n ns → Σ[ i ∈ Fin n ] Fin (ns i)
  ⊎Fin→ΣFin (suc n) ns (inl i) = zero , i
  ⊎Fin→ΣFin (suc n) ns (inr i) =
    let j , k = ⊎Fin→ΣFin n (λ i → ns (suc i)) i
     in suc j , k

  ΣFin→⊎Fin→ΣFin : ∀ n ns i → ⊎Fin→ΣFin n ns (ΣFin→⊎Fin n ns i) ≡ i
  ΣFin→⊎Fin→ΣFin (suc n) ns (zero  , j) = refl
  ΣFin→⊎Fin→ΣFin (suc n) ns (suc i , j) =
    cong (λ x → suc (x .fst) , x .snd) (ΣFin→⊎Fin→ΣFin n (ns ∘ suc) (i , j))

  ⊎Fin→ΣFin→⊎Fin : ∀ n ns i → ΣFin→⊎Fin n ns (⊎Fin→ΣFin n ns i) ≡ i
  ⊎Fin→ΣFin→⊎Fin (suc n) ns (inl i) = refl
  ⊎Fin→ΣFin→⊎Fin (suc n) ns (inr i) = cong inr (⊎Fin→ΣFin→⊎Fin n (ns ∘ suc) i)

  ΠFin→×Fin : ∀ n ns → ((i : Fin n) → Fin (ns i)) → ×Fin n ns
  ΠFin→×Fin zero    ns f = zero
  ΠFin→×Fin (suc n) ns f = f zero , ΠFin→×Fin n (ns ∘ suc) (f ∘ suc)

  ×Fin→ΠFin : ∀ n ns → ×Fin n ns → (i : Fin n) → Fin (ns i)
  ×Fin→ΠFin zero    ns xs       ()
  ×Fin→ΠFin (suc n) ns (x , xs) zero    = x
  ×Fin→ΠFin (suc n) ns (x , xs) (suc i) = ×Fin→ΠFin n (ns ∘ suc) xs i

  ×Fin→ΠFin→×Fin : ∀ n ns i → ΠFin→×Fin n ns (×Fin→ΠFin n ns i) ≡ i
  ×Fin→ΠFin→×Fin zero    ns zero     = refl
  ×Fin→ΠFin→×Fin (suc n) ns (i , is) = ΣPathP (refl , ×Fin→ΠFin→×Fin n (ns ∘ suc) is)

  ΠFin→×Fin→ΠFin : ∀ n ns f → ×Fin→ΠFin n ns (ΠFin→×Fin n ns f) ≡ f
  ΠFin→×Fin→ΠFin zero ns f = funExt λ ()
  ΠFin→×Fin→ΠFin (suc n) ns f = funExt λ
    { zero    → refl;
      (suc i) → funExt⁻ (ΠFin→×Fin→ΠFin n (ns ∘ suc) (f ∘ suc)) i
    }

  ×Fin→FinΠ′ : ∀ m n ns → Fin n × ×Fin m ns → Fin (n * ΠFin m ns)
  ×Fin→FinΠ′ zero    n       ns (i , _)      = inject* _ i
  ×Fin→FinΠ′ (suc m) (suc n) ns (zero  , is) = inject+ _ (×Fin→FinΠ′ m (ns zero) (ns ∘ suc) is)
  ×Fin→FinΠ′ (suc m) (suc n) ns (suc i , is) = raise _ (×Fin→FinΠ′ (suc m) n ns (i , is))
  
  ¬left-suc≡0 : ∀ {ℓ} {A : Type ℓ} {m} (i : Fin m ⊎ A) → ¬ map suc (λ x → x) i ≡ inl {A = Fin (suc m)} zero
  ¬left-suc≡0 (inl _) p = snotz (inl-inj p)
  ¬left-suc≡0 (inr _) p = inl≢inr (sym p)

  left-suc→inl : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} {m}
                   {g : A → B} {x : Fin m ⊎ A} {i : Fin m} →
                   map suc g x ≡ inl {A = Fin (suc m)} (suc i) → x ≡ inl i
  left-suc→inl {x = inl _} p = cong inl (injSucFin (inl-inj p))
  left-suc→inl {x = inr _} p = ⊥-rec (inl≢inr (sym p))

  right-id→inr :  ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃}
                    {f : A → C} {x : A ⊎ B} {b : B} →
                    map f (λ x → x) x ≡ inr {A = C} {B = B} b → x ≡ inr b
  right-id→inr {x = inl x} p = ⊥-rec (inl≢inr p)
  right-id→inr {x = inr x} p = cong inr (inr-inj p)

  inject+-splitAt : ∀ m {n} (i : Fin (m + n)) (j : Fin m) → splitAt m i ≡ inl j → inject+ n j ≡ i
  inject+-splitAt (suc m) zero    j       p = inject+0 _ j (sym (inl-inj p))
  inject+-splitAt (suc m) (suc i) zero    p = ⊥-rec (¬left-suc≡0 _ p)
  inject+-splitAt (suc m) (suc i) (suc j) p = cong suc (inject+-splitAt m i j (left-suc→inl p))

  raise-splitAt : ∀ m {n} (i : Fin (m + n)) (j : Fin n) → splitAt m i ≡ inr j → raise m j ≡ i
  raise-splitAt zero    i       j p = inr-inj (sym p)
  raise-splitAt (suc m) zero    j p = ⊥-rec (inl≢inr p)
  raise-splitAt (suc m) (suc i) j p = cong suc (raise-splitAt m i j (right-id→inr p))

splitAt-inject+ : ∀ m n i → splitAt m (inject+ n i) ≡ inl i
splitAt-inject+ (suc m) n zero    = refl
splitAt-inject+ (suc m) n (suc i) = cong (map suc (λ x -> x)) (splitAt-inject+ m n i)

splitAt-raise : ∀ m n i → splitAt m {n} (raise m i) ≡ inr i
splitAt-raise zero    n i = refl
splitAt-raise (suc m) n i = cong (map suc (λ x -> x)) (splitAt-raise m n i)

inject+-raise-splitAt : ∀ m n i → [ inject+ n , raise m ] (splitAt m i) ≡ i
inject+-raise-splitAt zero n i          = refl
inject+-raise-splitAt (suc m) n zero    = refl
inject+-raise-splitAt (suc m) n (suc i) =
  [ inject+ n , raise (suc m) ] (splitAt (suc m) (suc i)) ≡⟨ [,]-map-commute (splitAt m i) ⟩
  [ suc ∘ (inject+ n) , suc ∘ (raise m) ] (splitAt m i)    ≡⟨ sym ([,]-∘-distr suc (splitAt m i)) ⟩
  suc ([ inject+ n , raise m ] (splitAt m i))             ≡⟨ cong suc (inject+-raise-splitAt m n i) ⟩
  suc i                                                   ∎

decMap : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} →
           (A → B) → (B → A) → Dec A → Dec B
decMap f g (yes a) = yes (f a)
decMap f g (no ¬a) = no (¬a ∘ g)

∀-cons : ∀ {ℓ n} {P : Fin (suc n) → Type ℓ} → P zero → (∀ i → P (suc i)) → ∀ i → P i
∀-cons z s zero    = z
∀-cons z s (suc i) = s i

_×-dec_ : ∀ {ℓ₁ ℓ₂} {P : Type ℓ₁} {Q : Type ℓ₂} → Dec P → Dec Q → Dec (P × Q)
yes p ×-dec yes q = yes (p , q)
yes p ×-dec no ¬q = no λ (_ , q) → ¬q q
no ¬p ×-dec q?    = no λ (p , _) → ¬p p

_⊎-dec_ : ∀ {ℓ₁ ℓ₂} {P : Type ℓ₁} {Q : Type ℓ₂} → Dec P → Dec Q → Dec (P ⊎ Q)
yes p ⊎-dec q     = yes (inl p)
no ¬p ⊎-dec yes q = yes (inr q)
no ¬p ⊎-dec no ¬q = no [ ¬p , ¬q ]

<_,_> : ∀ {ℓ₁ ℓ₂ ℓ₃} {A : Type ℓ₁} {B : A → Type ℓ₂} {C : ∀ {x} → B x → Type ℓ₃}
        (f : (x : A) → B x) → ((x : A) → C (f x)) →
        ((x : A) → Σ (B x) C)
< f , g > x = (f x , g x)

decRec : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} {B : Type ℓ₂} (f : A → B) (g : ¬ A → B) → Dec A → B
decRec f g (yes a) = f a
decRec f g (no ¬a) = g ¬a

decFinSubset : ∀ {n ℓ₁ ℓ₂} {P : Fin n → Type ℓ₁} {Q : Fin n → Type ℓ₂} →
                 (∀ i → Dec (Q i)) → (∀ {i} → Q i → Dec (P i)) → Dec (∀ {i} → Q i → P i)
decFinSubset {zero} Q? P? = yes λ {}
decFinSubset {suc n} {P = P} {Q} Q? P? with Q? zero | ∀-cons {P = λ x → Q x → P x}
... | yes q | cons = decMap (uncurry λ p₀ rec {i} → cons (λ _ → p₀) (λ i → rec {i}) i)
                            < (λ f → f q) , (λ f {i} → f {suc i}) >
                            (P? q ×-dec decFinSubset (Q? ∘ suc) P?)
... | no ¬q | cons = decMap (λ f {i} → cons (⊥-rec ∘ ¬q) (λ x → f {x}) i)
                            (λ f {x} → f {suc x})
                            (decFinSubset (Q? ∘ suc) P?)

all? : ∀ {ℓ n} {P : Fin n → Type ℓ} → (∀ i → Dec (P i)) → Dec (∀ i → P i)
all? P? = decMap (λ p i → p tt)
                 (λ p {x} _ → p x)
                 (decFinSubset (λ _ → yes tt) λ {i} _ → P? i)

any? : ∀ {n ℓ} {P : Fin n → Type ℓ} → (∀ i → Dec (P i)) → Dec (Σ[ i ∈ Fin n ] P i)
any? {zero} P? = no (λ ())
any? {suc n} P? = decMap [ zero ,_ , (λ (i , p) → suc i , p) ]
                         (λ { (zero , p) → inl p; (suc i , p) → inr (i , p) })
                         (P? zero ⊎-dec any? (P? ∘ suc))

Search : ∀ {ℓ} {X : Type ℓ} {m} → Discrete X → (x : X) (f : Fin m → X) → Dec (fiber f x)
Search D x f = any? λ i → D (f i) x

Dec-inj : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂} → Discrete X → Discrete Y →
            (f : X → Y) → ∀ x₁ x₂ → Dec (f x₁ ≡ f x₂ → x₁ ≡ x₂)
Dec-inj Dx Dy f x₁ x₂ with Dx x₁ x₂ | Dy (f x₁) (f x₂)
... | yes p | _     = yes (λ _ → p)
... | no ¬p | yes p = no λ g → ¬p (g p)
... | no _  | no ¬p = yes (⊥-rec ∘ ¬p)

Unique : ∀ {ℓ} {X : Type ℓ} {m} → Discrete X → (f : Fin m → X) →
            Dec ((i j : Fin m) → f i ≡ f j → i ≡ j)
Unique D f = all? λ i → all? λ j → Dec-inj discreteFin D f i j

DecEmbedding : ∀ {ℓ} {X : Type ℓ} {m} → Discrete X → (f : Fin m → X) → Dec (isEmbedding f)
DecEmbedding D f with Unique D f
... | yes p = yes (injEmbedding isSetFin (Discrete→isSet D) (p _ _))
... | no ¬p = no λ g → ¬p λ i j → fst ∘ fst ∘ equiv-proof (g i j)

FinSurjection : ∀ {m n} (f : Fin m → Fin n) → Dec ((j : Fin n) → fiber f j)
FinSurjection f = all? λ i → Search discreteFin i f

isEquiv→Injection : ∀ {ℓ₁ ℓ₂} {X : Type ℓ₁} {Y : Type ℓ₂}
                      (f : X → Y) → isEquiv f → ∀ {x₁ x₂} → f x₁ ≡ f x₂ → x₁ ≡ x₂
isEquiv→Injection f p {x₁} {x₂} q =
  let (_ , s) = equiv-proof p (f x₁)
   in sym (λ i → fst (s (x₁ , refl) i)) ∙ λ i → fst (s (x₂ , sym q) i)

isFinEquiv : ∀ {m n} (f : Fin m → Fin n) → Dec (isEquiv f)
isFinEquiv f with Unique discreteFin f
... | no ¬p = no λ e → ¬p λ _ _ → isEquiv→Injection f e
... | yes p with FinSurjection f
...         | yes s = yes (isEmbedding×isSurjection→isEquiv (
                             injEmbedding isSetFin isSetFin (p _ _) , ∣_∣ ∘ s
                          ))
...         | no ¬s = no λ e → ¬s (fst ∘ equiv-proof e)

punchInᵢ≢i : ∀ {m} i (j : Fin m) → ¬ i ≡ punchIn i j
punchInᵢ≢i zero    j       = znots
punchInᵢ≢i (suc i) zero    = snotz
punchInᵢ≢i (suc i) (suc j) = punchInᵢ≢i i j ∘ injSucFin

punchOut-cong : ∀ {n} (i : Fin (suc n)) {j k} {i≢j : ¬ i ≡ j} {i≢k : ¬ i ≡ k} →
                  j ≡ k → punchOut i≢j ≡ punchOut i≢k
punchOut-cong zero {zero}         {i≢j = 0≢0}  = ⊥-rec (0≢0 refl)
punchOut-cong zero {suc j} {zero} {i≢k = 0≢0}  = ⊥-rec (0≢0 refl)
punchOut-cong zero {suc j} {suc k}             = injSucFin
punchOut-cong {suc n} (suc i) {zero}  {zero} _ = refl
punchOut-cong {suc n} (suc i) {zero}  {suc k}  = ⊥-rec ∘ znots
punchOut-cong {suc n} (suc i) {suc j} {zero}   = ⊥-rec ∘ snotz
punchOut-cong {suc n} (suc i) {suc j} {suc k}  = cong suc ∘ punchOut-cong i ∘ injSucFin

punchOut-cong′ : ∀ {n} (i : Fin (suc n)) {j k} {p : ¬ i ≡ j} (q : j ≡ k) →
                       punchOut p ≡ punchOut (p ∘ (_∙ sym q))
punchOut-cong′ i q = punchOut-cong i q

punchIn-punchOut : ∀ {m} {i j : Fin (suc m)} (i≢j : ¬ i ≡ j) →
                     punchIn i (punchOut i≢j) ≡ j
punchIn-punchOut {_}     {zero}  {zero}  i≢j = ⊥-rec (i≢j refl)
punchIn-punchOut {_}     {zero}  {suc j} i≢j = refl
punchIn-punchOut {suc m} {suc i} {zero}  i≢j = refl
punchIn-punchOut {suc m} {suc i} {suc j} i≢j = cong suc (punchIn-punchOut (i≢j ∘ cong suc))

punchOut-punchIn : ∀ {n} i {j : Fin n} → punchOut {i = i} {j = punchIn i j} (punchInᵢ≢i i j) ≡ j
punchOut-punchIn zero    {j}     = refl
punchOut-punchIn (suc i) {zero}  = refl
punchOut-punchIn (suc i) {suc j} = cong (Fin.suc) (punchOut-cong i refl ∙ punchOut-punchIn i)

open Iso

remove : ∀ {m n} (i : Fin (suc m)) → Iso (Fin (suc m)) (Fin (suc n)) → Iso (Fin m) (Fin n)
remove {m} {n} i I = iso to from sec ret
  where
    to-punchOut : ∀ {j : Fin m} → ¬ fun I i ≡ fun I (punchIn i j)
    to-punchOut = punchInᵢ≢i _ _ ∘ isoFunInjective I _ _

    from-punchOut : ∀ {j : Fin n} → ¬ i ≡ inv I (punchIn (fun I i) j)
    from-punchOut {j} p = punchInᵢ≢i (fun I i) j (cong (fun I) p ∙ rightInv I _)

    to : Fin m → Fin n
    to j = punchOut (to-punchOut {j})

    from : Fin n → Fin m
    from j = punchOut {j = inv I (punchIn (fun I i) j)} from-punchOut

    sec : section to from
    sec j =
      to (from j) ≡⟨ punchOut-cong′ (fun I i) (cong (fun I) (punchIn-punchOut {i = i} _)) ⟩
      _           ≡⟨ punchOut-cong (fun I i) (rightInv I _) ⟩
      _           ≡⟨ punchOut-punchIn (fun I i) ⟩
      j           ∎

    ret : retract to from
    ret j =
      from (to j) ≡⟨ punchOut-cong′ i (cong (inv I) (punchIn-punchOut {i = fun I i} _)) ⟩
      _           ≡⟨ punchOut-cong i (leftInv I _) ⟩
      _           ≡⟨ punchOut-punchIn i ⟩
      j           ∎

Fin-inj : ∀ {m n} → Iso (Fin m) (Fin n) → m ≡ n
Fin-inj {zero}  {zero}  I = refl
Fin-inj {zero}  {suc n} I = ⊥-rec (¬Fin0 (inv I zero))
Fin-inj {suc m} {zero}  I = ⊥-rec (¬Fin0 (fun I zero))
Fin-inj {suc m} {suc n} I = cong suc (Fin-inj (remove zero I))

finiteChoice : ∀ {ℓ} n {B : Fin n → Type ℓ} → ((i : Fin n) → ∥ B i ∥) → ∥ ((i : Fin n) → B i) ∥
finiteChoice zero f = ∣ (λ ()) ∣
finiteChoice (suc n) f =
  let ∥g∥ = finiteChoice n (f ∘ suc)
   in p-rec propTruncIsProp (λ b → p-rec propTruncIsProp (∣_∣ ∘ ∀-cons b) ∥g∥) (f zero)

finiteChoice₂ : ∀ {ℓ} n (ns : Fin n → ℕ)
                  {C : (i : Fin n) → Fin (ns i) → Type ℓ} →
                  ((i : Fin n) (j : Fin (ns i)) → ∥ C i j ∥) →
                  ∥ ((i : Fin n) (j : Fin (ns i)) → C i j) ∥
finiteChoice₂ zero    _  _ = ∣ (λ ()) ∣
finiteChoice₂ (suc n) ns f =
  let ∥g∥  = finiteChoice (ns zero) (f zero)
      ∥gs∥ = finiteChoice₂ n (ns ∘ suc) (f ∘ suc)
   in p-rec propTruncIsProp (λ g → p-rec propTruncIsProp (∣_∣ ∘ ∀-cons g) ∥gs∥) ∥g∥

congIso₂′ : ∀ {ℓ₁ ℓ₂} (_∙_ : Type ℓ₁ → Type ℓ₂ → Type (ℓ-max ℓ₁ ℓ₂)) →
           ∀ {A B C D} → Iso A B → Iso C D → Iso (A ∙ C) (B ∙ D)
congIso₂′ _∙_ {A = A} {C = C} I₁ I₂
  = subst (Iso (A ∙ C)) (cong₂ _∙_ (isoToPath I₁) (isoToPath I₂)) (idIso {A = A ∙ C})

finiteClosure : ∀ {ℓ₁ ℓ₂} {A : Type ℓ₁} (B : A → Type ℓ₂)
                  (_∙_ : A → A → A) (ε : A)
                  (_+_ : Type ℓ₂ → Type ℓ₂ → Type ℓ₂) →
                  (∀ a₁ a₂ → Iso (B a₁ + B a₂) (B (a₁ ∙ a₂))) →
                  (n : ℕ) (as : Fin n → A) →
                  Iso (finiteFold _+_ (B ε) n (B ∘ as)) (B (finiteFold _∙_ ε n as))
finiteClosure B _∙_ ε _+_ is zero as = idIso
finiteClosure B _∙_ ε _+_ is (suc n) as =
  let j = finiteClosure B _∙_ ε _+_ is n (as ∘ suc)
      k = is (as zero) (finiteFold _∙_ ε n (as ∘ suc))
   in compIso (congIso₂′ _+_ idIso j) k

Fin⊎↔Fin+ : ∀ m n → Iso (Fin m ⊎ Fin n) (Fin (m + n))
fun      (Fin⊎↔Fin+ m n) = [ inject+ n , raise m ]
inv      (Fin⊎↔Fin+ m n) = splitAt m
rightInv (Fin⊎↔Fin+ m n) = inject+-raise-splitAt m n
leftInv  (Fin⊎↔Fin+ m n) = Sum.elim (splitAt-inject+ m n) (splitAt-raise m n)

ΣFin↔⊎Fin : ∀ n ns → Iso (Σ[ i ∈ Fin n ] Fin (ns i)) (⊎Fin n ns)
fun      (ΣFin↔⊎Fin n ns) = ΣFin→⊎Fin n ns
inv      (ΣFin↔⊎Fin n ns) = ⊎Fin→ΣFin n ns
rightInv (ΣFin↔⊎Fin n ns) = ⊎Fin→ΣFin→⊎Fin n ns
leftInv  (ΣFin↔⊎Fin n ns) = ΣFin→⊎Fin→ΣFin n ns

ΠFin↔×Fin : ∀ n ns → Iso ((i : Fin n) → Fin (ns i)) (×Fin n ns)
fun      (ΠFin↔×Fin n ns) = ΠFin→×Fin n ns
inv      (ΠFin↔×Fin n ns) = ×Fin→ΠFin n ns
rightInv (ΠFin↔×Fin n ns) = ×Fin→ΠFin→×Fin n ns
leftInv  (ΠFin↔×Fin n ns) = ΠFin→×Fin→ΠFin n ns

⊎Fin↔FinΣ : ∀ n ns → Iso (⊎Fin n ns) (Fin (ΣFin n ns))
⊎Fin↔FinΣ = finiteClosure Fin _+_ 0 _⊎_ Fin⊎↔Fin+

ΣFin↔FinΣ : ∀ n ns → Iso (Σ[ i ∈ Fin n ] Fin (ns i)) (Fin (ΣFin n ns))
ΣFin↔FinΣ n ns = compIso (ΣFin↔⊎Fin n ns) (⊎Fin↔FinΣ n ns)

×Fin↔Fin* : ∀ m n → Iso (Fin m × Fin n) (Fin (m * n))
×Fin↔Fin* m n = compIso (ΣFin↔FinΣ m λ _ → n)
                        (subst (Iso (Fin (ΣFin m λ _ → n)) ∘ Fin)
                               (ΣFin-const≡* m n) idIso)
  where
    ΣFin-const≡* : ∀ m n → ΣFin m (λ _ → n) ≡ m * n
    ΣFin-const≡* zero    n = refl
    ΣFin-const≡* (suc m) n = cong (n +_) (ΣFin-const≡* m n)

×Fin↔FinΠ : ∀ n ns → Iso (×Fin n ns) (Fin (ΠFin n ns))
×Fin↔FinΠ = finiteClosure Fin _*_ 1 _×_ ×Fin↔Fin*

ΠFin↔FinΠ : ∀ n ns → Iso ((i : Fin n) → Fin (ns i)) (Fin (ΠFin n ns))
ΠFin↔FinΠ n ns = compIso (ΠFin↔×Fin n ns) (×Fin↔FinΠ n ns)

_^_ : ℕ → ℕ → ℕ
m ^ 0     = 1
m ^ suc n = m * (m ^ n)

→Fin↔Fin^ : ∀ m n → Iso (Fin m → Fin n) (Fin (n ^ m))
→Fin↔Fin^ m n = compIso (ΠFin↔FinΠ m λ _ → n)
                        (subst (Iso (Fin (ΠFin m λ _ → n)) ∘ Fin)
                               (ΠFin-const≡^ m n) idIso)
  where
    ΠFin-const≡^ : ∀ m n → ΠFin m (λ _ → n) ≡ (n ^ m)
    ΠFin-const≡^ zero    n = refl
    ΠFin-const≡^ (suc m) n = cong (n *_) (ΠFin-const≡^ m n)

Fin/ : ∀ m i → Iso (Σ[ j ∈ Fin (suc m) ] ¬ i ≡ j) (Fin m)
fun      (Fin/ m i) (j , p) = punchOut p
inv      (Fin/ m i) j       = punchIn i j , punchInᵢ≢i i j
rightInv (Fin/ m i) _       = punchOut-punchIn i
leftInv  (Fin/ m i) (j , p) = ΣPathP (punchIn-punchOut p , isProp→PathP (λ _ → isProp¬ _) _ _)
