{-# OPTIONS --cubical --safe #-}

module Operad.Fin.Base where

open import Cubical.Data.Empty renaming (rec to ⊥-rec)
open import Cubical.Data.FinData
open import Cubical.Data.Nat renaming (_·_ to _*_)
open import Cubical.Data.Nat.Order
open import Cubical.Data.Sigma
open import Cubical.Data.Sum

open import Cubical.Foundations.Function
open import Cubical.Foundations.Prelude

open import Cubical.Relation.Nullary

finiteFold : ∀ {ℓ} {A : Type ℓ} (_∙_ : A → A → A) (ε : A) →
             ∀ n → (Fin n → A) → A
finiteFold _∙_ ε zero    as = ε
finiteFold _∙_ ε (suc n) as = as zero ∙ finiteFold _∙_ ε n (as ∘ suc)

ΣFin : ∀ n → (Fin n → ℕ) → ℕ
ΣFin = finiteFold _+_ 0

ΠFin : ∀ n → (Fin n → ℕ) → ℕ
ΠFin = finiteFold _*_ 1

⊎Fin : ∀ n → (Fin n → ℕ) → Type ℓ-zero
⊎Fin n ns = finiteFold _⊎_ (Fin 0) n (Fin ∘ ns)

×Fin : ∀ n → (Fin n → ℕ) → Type ℓ-zero
×Fin n ns = finiteFold _×_ (Fin 1) n (Fin ∘ ns)

inject+ : ∀ {m} n → Fin m → Fin (m + n)
inject+ {suc m} n zero    = zero
inject+ {suc m} n (suc i) = suc (inject+ n i)

inject+′ : ∀ {m} n → Fin m → Fin (n + m)
inject+′ {suc m} zero    i = i
inject+′ {suc m} (suc n) i = suc (inject+′ n i)

inject* : ∀ {m} n → Fin m → Fin (m * suc n)
inject* {suc m} n zero    = zero
inject* {suc m} n (suc i) = suc (inject+′ n (inject* n i))

raise : ∀ m {n} → Fin n → Fin (m + n)
raise zero i  = i
raise (suc m) = suc ∘ raise m

splitAt : ∀ m {n} → Fin (m + n) → Fin m ⊎ Fin n
splitAt zero    i       = inr i
splitAt (suc m) zero    = inl zero
splitAt (suc m) (suc i) = map suc (λ x → x) (splitAt m i)

fromℕ< : ∀ {m n} → m < n → Fin n
fromℕ< {zero}  {zero}  p = ⊥-rec (¬m<m p)
fromℕ< {zero}  {suc n} p = zero
fromℕ< {suc m} {zero}  p = ⊥-rec (¬-<-zero p)
fromℕ< {suc m} {suc n} p = suc (fromℕ< (pred-≤-pred p))

punchOut : ∀ {m} {i j : Fin (suc m)} → ¬ i ≡ j → Fin m
punchOut {_}     {zero}   {zero}  i≢j = ⊥-rec (i≢j refl)
punchOut {_}     {zero}   {suc j} _   = j
punchOut {suc m} {suc i}  {zero}  _   = zero
punchOut {suc m} {suc i}  {suc j} i≢j = suc (punchOut (i≢j ∘ cong suc))

punchIn : ∀ {m} → Fin (suc m) → Fin m → Fin (suc m)
punchIn zero    j       = suc j
punchIn (suc i) zero    = zero
punchIn (suc i) (suc j) = suc (punchIn i j)
