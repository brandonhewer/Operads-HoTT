{-# OPTIONS --cubical --no-import-sorts --safe #-}

module Operad.Monad.Base where

open import Category.Functor

open import Cubical.Data.FinData
open import Cubical.Data.Sigma hiding (comp)
open import Cubical.Data.Unit renaming (Unit to ⊤)

open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws hiding (assoc)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Path
open import Cubical.Foundations.Prelude hiding (comp) renaming (ℓ-max to _⊔_)
open import Cubical.Foundations.Transport
open import Cubical.Foundations.Univalence

open import Operad.Base
open import Operad.FinSet.Small
open import Operad.Free renaming (Op to ηF)
open import Operad.Instance.Endo
open import Operad.Morphism

private
  variable
    a b c ℓ₁ ℓ₂ ℓ₃ : Level
    A : Type a
    B : Type b
    C : Type c
    O : Operad ℓ₁ ℓ₂

  transp-filler : (A : I → Type ℓ₁) (x : A i0) →
                  PathP (λ i → A i) x (transp A i0 x)
  transp-filler A x i = transp (λ j → A (i ∧ j)) (~ i) x            

  transp-fillerExt : (A : I → Type ℓ₁) →
                     PathP (λ i → A i0 → A i) (λ x → x) (transp A i0)
  transp-fillerExt A i x = transp-filler A x i

  transp⁻-fillerExt : (A : I → Type ℓ₁) →
                      PathP (λ i → A i → A i0) (λ x → x) (transp (λ i → A (~ i)) i0)
  transp⁻-fillerExt A i x = transp (λ j → A (i ∧ ~ j)) (~ i) x

  transp⁻Transp : (A : I → Type ℓ₁) (a : A i0) →
                  transp (λ i → A (~ i)) i0 (transp A i0 a) ≡ a
  transp⁻Transp A a j = transp⁻-fillerExt A (~ j) (transp-fillerExt A (~ j) a)

  transpInv : (A : I → Type ℓ₁) (x : A i0) {y : A i1} →
            transp A i0 x ≡ y → transp (λ i → A (~ i)) i0 y ≡ x
  transpInv A x =
    J (λ z _ → transp (λ i → A (~ i)) i0 z ≡ x) (transp⁻Transp A x)

  fromPathP⁻ : (A : I → Type ℓ₁) {x : A i0} {y : A i1} →
               PathP A x y → transp (λ i → A (~ i)) i0 y ≡ x 
  fromPathP⁻ A {x} p = transpInv A x (fromPathP p)

  transport-distr : {A B C : Type ℓ₁} (p : A ≡ B) (q : B ≡ C) →
                    transport (p ∙ q) ≡ transport q ∘ transport p
  transport-distr {A = A} p q =
    funExt λ a i →
      transp (λ j → q j) i0
        (transp (λ j → p j) i0
          (transp (λ _ → A) i a))

  uaβ⁻ : {A B : Type ℓ₁} (e : A ≃ B) (x : B) → transport (sym (ua e)) x ≡ invEq e x
  uaβ⁻ e x = cong (λ p → transport p x) (sym (uaInvEquiv e)) ∙ uaβ (invEquiv e) x

open Operad

record OpM (O : Operad ℓ₁ ℓ₂) (X : Type ℓ₃) : Type (ℓ-max (ℓ-suc ℓ₁) (ℓ-max ℓ₂ ℓ₃)) where
  field
    Idx  : FinSetD ℓ₁
    Op   : Ops O Idx
    Data : El Idx → X

open OpM

OpM≡ : {x y : OpM O A} (p : Idx x ≡ Idx y) →
       PathP (λ i → Ops O (p i)) (Op x) (Op y) →
       PathP (λ i → El (p i) → A) (Data x) (Data y) → x ≡ y
Idx  (OpM≡ p q r i) = p i
Op   (OpM≡ p q r i) = q i
Data (OpM≡ p q r i) = r i

compM : (oa : OpM O A) → (El (Idx oa) → A → OpM O B) → OpM O B
Idx  (compM oa f)         = ΣF (Idx oa) λ i → Idx (f i (Data oa i))
Op   (compM {O = O} oa f) = comp O _ _ (Op oa) λ i → Op (f i (Data oa i))
Data (compM oa f) (i , j) = Data (f i (Data oa i)) j

_>>=_ : (oa : OpM O A) → (El (Idx oa) × A → OpM O B) → OpM O B
x >>= f = compM x (curry f)

_>>=′_ : OpM O A → (A → OpM O B) → OpM O B
x >>=′ f = compM x (λ _ → f)

join : OpM O (OpM O A) → OpM O A
join = _>>=′ λ x → x

return : A → OpM O A
Idx  (return x)         = ⊤F
Op   (return {O = O} x) = id O
Data (return x) _       = x

_<$>_ : (A → B) → OpM O A → OpM O B
Idx  (f <$> x) = Idx x
Op   (f <$> x) = Op x
Data (f <$> x) = f ∘ Data x

join-return : (x : OpM O A) → join (return x) ≡ join (return <$> x)
join-return {ℓ₁} {O = O} x =
  OpM≡ (un _ _ (isoToEquiv (L≡R _)))
       (toPathP (
         cong (λ p → subst (Ops O) p (comp O ⊤F (λ _ → Idx x) (id O) (λ _ → Op x)))
              (congEl-inj _ _ lem) ∙
         substComposite (Ops O) (ΣIdL _) (sym (ΣIdR _)) _ ∙
         cong (subst (Ops O) (sym (ΣIdR _))) (fromPathP (idl O _ (λ _ → Op x))) ∙
         fromPathP⁻ _ (idr O _ _)
       ))
       (ua→ λ { (lift zero , a) → refl })
  where
    open Iso

    L≡R : (A : Lift {j = ℓ₂} (Fin 1) → Type ℓ₁) →
          Iso (Σ (Lift (Fin 1)) A) (Σ {b = ℓ₂} (A (lift zero)) λ _ → Lift (Fin 1))
    fun      (L≡R A) (lift zero , a) = a , lift zero
    inv      (L≡R A) (a , lift zero) = lift zero , a
    rightInv (L≡R A) (a , lift zero) = refl
    leftInv  (L≡R A) (lift zero , a) = refl

    lem : isoToPath (L≡R _) ≡
          cong El (ΣIdL (λ _ → Idx x) ∙ sym (ΣIdR _))
    lem =
      isInjectiveTransport (funExt λ { (lift zero , a) →
        uaβ (isoToEquiv (L≡R (λ _ → El (Idx x)))) (lift zero , a) ∙
        sym (
          funExt⁻ (transport-distr (isoToPath (ΣIdLIso {ℓ₂ = ℓ₁} {A = λ _ → El (Idx x)}))
                                   (sym (isoToPath ΣIdRIso)))
                  (lift zero , a) ∙
          cong (transport (sym (isoToPath ΣIdRIso)))
               (uaβ (isoToEquiv (ΣIdLIso {ℓ₂ = ℓ₁} {A = λ _ → El (Idx x)}))
                    (lift zero , a)) ∙
          uaβ⁻ (isoToEquiv ΣIdRIso) a
        )
      })

join-assoc : (x : OpM O (OpM O (OpM O A))) →
             join (join x) ≡ join (join <$> x)
join-assoc {O = O} x =
  OpM≡ (ΣAssoc _ _ _) (assoc O _ _ _ _ _ _)
       (ua→ λ { ((a , b) , c) → refl })

>>=<$> : (f : A → B) (x : OpM O A) → (x >>=′ (return ∘ f)) ≡ f <$> x
>>=<$> {O = O} f x =
  OpM≡ (ΣIdR _) (idr O _ _) (ua→ λ { (a , lift zero) → refl })

_<*>_ : OpM O (A → B) → OpM O A → OpM O B
of <*> oa = of >>=′ (_<$> oa)

pure<*>_ : (x : OpM O A) → return (λ x → x) <*> x ≡ x
pure<*>_ {O = O} x =
  OpM≡ (ΣIdL _) (idl O _ _) (ua→ λ { (lift zero , a) → refl })

liftO2 : (A → B → C) → OpM O A → OpM O B → OpM O C
liftO2 f oa ob = oa >>=′ λ a → (f a <$> ob)

runOpM : (∀ X → Ops O X → (El X → A) → A) → OpM O A → A
runOpM α x = α (Idx x) (Op x) (Data x)

mkOpM : (∀ X → Ops O X → (El X → B) → B) →
        (x : OpM O A) → (El (Idx x) → B) → B
mkOpM f x g = f (Idx x) (Op x) g

FreeOpM : (K : FinSetD ℓ₁ → Type ℓ₂) → Type ℓ₃ → Type _
FreeOpM K = OpM (FreeOperad K)

_[_↑_] : (K : FinSetD ℓ₁ → Type ℓ₂) → ∀ {X} → K X → (El X → FreeOpM K A) → FreeOpM K A
Idx  (_[_↑_] K {X} k f)    = ΣF X (Idx ∘ f)
Op   (K [ k ↑ f ])         = comp (FreeOperad K) _ _ (ηF _ k) (Op ∘ f)
Data (K [ k ↑ f ]) (i , j) = Data (f i) j

runFreeOpM :
  (K : FinSetD ℓ₁ → Type ℓ₂) →
  isSet A → (∀ {X} → K X → (El X → A) → A) →
  FreeOpM K A → A
runFreeOpM K isSetA f =
  runOpM (interpret′ K (Endo isSetA) λ _ → f)

mkFreeOpM :
  (K : FinSetD ℓ₁ → Type ℓ₂) →
  isSet B → (∀ {X} → K X → (El X → B) → B) →
  (x : FreeOpM K A) → (El (Idx x) → B) → B
mkFreeOpM K isSetB f =
  mkOpM (interpret′ K (Endo isSetB) λ _ → f)

-- EXAMPLE

open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Empty
open import Cubical.Data.FinData

_⊛_ : ℕ → Type ℓ₁ → Type ℓ₁
0           ⊛ A = Lift ⊤
1           ⊛ A = A
suc (suc n) ⊛ A = A × (suc n ⊛ A)

⊛-idx : ∀ {n} {A : Type ℓ₁} → n ⊛ A → Fin n → A
⊛-idx {n = 1}           a        _       = a
⊛-idx {n = suc (suc n)} (a , as) zero    = a
⊛-idx {n = suc (suc n)} (a , as) (suc i) = ⊛-idx as i

data ℕOps : FinSetD ℓ-zero → Type₁ where
  constN    : (n : ℕ) → ℕOps (FinD 0)
  succ      : ℕOps (FinD 1)
  plus mult : ℕOps (FinD 2)

-- OpSize : ∀ {A} → ℕOps A → ℕ
-- ∀ {A} → (x : ℕOps A) → Iso A (Fin (OpSize x))

ℕOps-S : ∀ {A} → ℕOps A → ℕ
ℕOps-S (constN _) = 0
ℕOps-S succ       = 1
ℕOps-S plus       = 2
ℕOps-S mult       = 2

pattern 0F = zero
pattern 1F = suc zero

ℕOpM : (A : Type ℓ₁) → Type _
ℕOpM = FreeOpM ℕOps

Indices : ℕOpM A → ℕ
Indices x = {!!}

_↑_ : ∀ {n} → ℕOps (FinD n) → (n ⊛ ℕOpM A) → ℕOpM A
x ↑ xs = ℕOps [ x ↑ ⊛-idx xs ]

_∘ⁿ_ : (x : ℕOpM A) → (Indices x ⊛ ℕOpM A) → ℕOpM A
x ∘ⁿ xs = {!!}

constM : {A : Type ℓ₁} → ℕ → ℕOpM A
constM n = constN n ↑ _

succM : {A : Type ℓ₁} → ℕOpM A → ℕOpM A
succM x = succ ↑ x

_+M_ : {A : Type ℓ₁} → ℕOpM A → ℕOpM A → ℕOpM A
x +M y = plus ↑ (x , y) 

_*M_ : {A : Type ℓ₁} → ℕOpM A → ℕOpM A → ℕOpM A
x *M y = mult ↑ (x , y)

intℕOps : ∀ {A} → ℕOps A → (El A → ℕ) → ℕ
intℕOps (constN n) xs = n
intℕOps succ       xs = xs zero
intℕOps plus       xs = xs zero + xs (suc zero)
intℕOps mult       xs = xs zero * xs (suc zero)

mkℕOp : (x : ℕOpM A) → (El (Idx x) → ℕ) → ℕ
mkℕOp = mkFreeOpM ℕOps isSetℕ intℕOps

eval : ℕOpM ℕ → ℕ
eval = runFreeOpM ℕOps isSetℕ intℕOps

ex : {A : Type ℓ₁} → ℕOpM ℕ → ℕOpM ℕ → ℕOpM ℕ
ex x y = {!!}
  where
    exFun : El (Idx (x +M y)) → ℕ → ℕ
    exFun (zero , _)  = 2 +_
    exFun (suc _ , _) = 3 *_

z : ℕOpM ℕ
z = return 0

ten : ℕOpM ℕ
ten = return 10

_^_ : ℕ → ℕ → ℕ
m ^ zero = suc zero
m ^ suc n = m * (m ^ n)

-- Builds fib operation
fibonacci : (n : ℕ) → ℕOpM ℕ
fibonacci 0 = return 0
fibonacci 1 = return 1
fibonacci (suc (suc n)) = fibonacci (suc n) +M fibonacci n

powerTwo : (n : ℕ) → ℕOpM ℕ
powerTwo 0 = return 1
powerTwo (suc n) = powerTwo n +M powerTwo n

one : ℕOpM ℕ
one = return 1

two : ℕOpM ℕ
two = return 2

exM : ℕOpM ℕ
exM = do
  (i , x) <- one +M two
  (j , y) <- (return x) *M two
  z <- {!(one +M two) ∘ⁿ ?!}
  fibonacci y

t : ℕ
t = eval exM

{-
          +
         / \
        /   \
       1     2
      / \   / \
     2   2 4   4
-}


{-

                           +
                          / \
                         /   \
                        +     +
                       / \   / \
                      1   1 1   1
-}

-- 20

-- y : 34
