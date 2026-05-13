{-# OPTIONS --cubical #-}
-- Constructive proofs of the three monad laws for OpM O.
-- The same skeleton as Endo-idl / Endo-idr / Endo-assoc in HoTTOperads.Operad.Endo:
-- each law is a triple of paths on Index, Op, Data, with the Data path discharged
-- via subst over the universe coherence (⟦⅀Idl⟧ / ⟦⅀Idr⟧ / ⟦⅀Assoc⟧) plus
-- ua-ungluePathExt.
module HoTTOperads.Monad.Laws where

open import Cubical.Foundations.Prelude hiding (J)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.Monad.Base
open import HoTTOperads.Monad.Functor
open import HoTTOperads.Monad.Composition

private
  variable
    ℓc ℓe ℓk ℓx : Level

module _ {𝒰 : Universe ℓc ℓe} {K : Universe.Code 𝒰 → Type ℓk} (O : Operad 𝒰 K) where
  open Universe 𝒰
  open Operad O

  opaque
    -- Left unit law.
    -- Both sides are OpM O X. After reducing join (return x) the LHS data field
    -- becomes (λ ab → D (snd (⟦⅀⟧ 𝜏 (λ _ → I) ab))), which is definitionally
    -- D ∘ equivFun (⅀Idl≃ I) because ⅀Idl≃ collapses to (snd ∘ ⟦⅀⟧ 𝜏 _) under η.
    join-return₁ : {X : Type ℓx} (x : OpM O X) → join O (return O x) ≡ x
    join-return₁ {X = X} (I ▷ k ▷ D) i =
      Inj (⅀Idl≃ I) i ▷ idl I k i ▷ data-path i
      where
        lhs : El (⅀ 𝜏 (λ _ → I)) → X
        lhs ab = D (snd (equivFun (⟦⅀⟧ 𝜏 (λ _ → I)) ab))

        path-ua : PathP (λ i → ua (⅀Idl≃ I) i → X) lhs D
        path-ua i el = D (ua-unglue (⅀Idl≃ I) i el)

        data-path : PathP (λ i → El (Inj (⅀Idl≃ I) i) → X) lhs D
        data-path = subst (λ p → PathP (λ i → p i → X) lhs D) (⟦⅀Idl⟧ I) path-ua

    -- Right unit law.
    -- After reducing join (return <$> x) the LHS data field becomes
    -- (λ ab → D (fst (⟦⅀⟧ I (λ _ → 𝜏) ab))) = D ∘ equivFun (⅀Idr≃ I) definitionally.
    join-return₂ : {X : Type ℓx} (x : OpM O X) → join O (return O <$> x) ≡ x
    join-return₂ {X = X} (I ▷ k ▷ D) i =
      Inj (⅀Idr≃ I) i ▷ idr I k i ▷ data-path i
      where
        lhs : El (⅀ I (λ _ → 𝜏)) → X
        lhs ab = D (fst (equivFun (⟦⅀⟧ I (λ _ → 𝜏)) ab))

        path-ua : PathP (λ i → ua (⅀Idr≃ I) i → X) lhs D
        path-ua i el = D (ua-unglue (⅀Idr≃ I) i el)

        data-path : PathP (λ i → El (Inj (⅀Idr≃ I) i) → X) lhs D
        data-path = subst (λ p → PathP (λ i → p i → X) lhs D) (⟦⅀Idr⟧ I) path-ua

    -- Associativity.
    -- Natural direction of ⅀Assoc≃ / Operad.assoc is nested-right → nested-left.
    --   join ((join O) <$> y)  is nested-right
    --   join (join y)          is nested-left
    -- We build aux : nested-right ≡ nested-left and return sym aux.
    join-assoc : {X : Type ℓx} (y : OpM O (OpM O (OpM O X)))
               → join O (join O y) ≡ join O ((join O) <$> y)
    join-assoc {X = X} (I ▷ k ▷ D) = sym aux
      where
        -- Destructure y two levels deep.
        J : El I → Code
        J a = Index (D a)
        ks : (a : El I) → K (J a)
        ks a = Op (D a)
        E : (a : El I) → El (J a) → OpM O X
        E a = Data (D a)

        M : (a : El I) → El (J a) → Code
        M a b = Index (E a b)
        kss : (a : El I) (b : El (J a)) → K (M a b)
        kss a b = Op (E a b)
        F : (a : El I) (b : El (J a)) → El (M a b) → X
        F a b = Data (E a b)

        data-NR : El (⅀ I (λ a → ⅀ (J a) (M a))) → X
        data-NR abc =
          let aBc = equivFun (⟦⅀⟧ I (λ a → ⅀ (J a) (M a))) abc
              a = fst aBc
              bc = snd aBc
              bC = equivFun (⟦⅀⟧ (J a) (M a)) bc
          in F a (fst bC) (snd bC)

        data-NL : El (⅀ (⅀ I J) (⅀Assoc-C' I J M)) → X
        data-NL abc =
          let abC = equivFun (⟦⅀⟧ (⅀ I J) (⅀Assoc-C' I J M)) abc
              ab = fst abC
              aB = equivFun (⟦⅀⟧ I J) ab
          in F (fst aB) (snd aB) (snd abC)

        -- B' : the second-component family of the target Σ in Σ-cong-equiv-fst (⟦⅀⟧ I J).
        -- B' (a , b) = El (M a b).
        B' : Σ[ a ∈ El I ] El (J a) → Type ℓe
        B' ab-pair = El (M (fst ab-pair) (snd ab-pair))

        -- The homogeneous pointwise equation. Computing equivFun (⅀Assoc≃ I J M) abc
        -- (a , bc) → (a , (b , c)) → ((a , b) , c) → (ab* , c-bd) → invEq e₄ (ab* , c-bd)
        -- where ab* = invEq (⟦⅀⟧ I J) (a , b) and c-bd is a subst of c.
        -- Then data-NL of this unfolds to F (fst (equivFun (⟦⅀⟧ I J) α)) (snd …) γ
        -- with (α , γ) = equivFun e₄ (invEq e₄ (ab* , c-bd)). Two secEq insertions
        -- (one for e₄, one for ⟦⅀⟧ I J) slide (a , b , c) into this form.
        homog-pt : (abc : El (⅀ I (λ a → ⅀ (J a) (M a))))
                 → data-NR abc ≡ data-NL (equivFun (⅀Assoc≃ I J M) abc)
        homog-pt abc =
          let aBc : Σ[ a ∈ El I ] El (⅀ (J a) (M a))
              aBc = equivFun (⟦⅀⟧ I (λ a → ⅀ (J a) (M a))) abc
              a : El I
              a = fst aBc
              bc : El (⅀ (J a) (M a))
              bc = snd aBc
              bC : Σ[ b ∈ El (J a) ] El (M a b)
              bC = equivFun (⟦⅀⟧ (J a) (M a)) bc
              b : El (J a)
              b = fst bC
              c : El (M a b)
              c = snd bC

              ab* : El (⅀ I J)
              ab* = invEq (⟦⅀⟧ I J) (a , b)

              c-bd : El (⅀Assoc-C' I J M ab*)
              c-bd = subst B' (sym (secEq (⟦⅀⟧ I J) (a , b))) c

              -- step1 slides (a , b , c) along sym (secEq (⟦⅀⟧ I J) (a , b)),
              -- transporting c heterogeneously into c-bd via a transport filler.
              step1 : F a b c
                    ≡ F (fst (equivFun (⟦⅀⟧ I J) ab*))
                        (snd (equivFun (⟦⅀⟧ I J) ab*))
                        c-bd
              step1 i =
                let p  = sym (secEq (⟦⅀⟧ I J) (a , b)) i
                    c-i = transp (λ k → B' (sym (secEq (⟦⅀⟧ I J) (a , b)) (i ∧ k)))
                                 (~ i) c
                in F (fst p) (snd p) c-i

              -- step2 slides (ab* , c-bd) along sym (secEq (⟦⅀⟧ (⅀ I J) …) (ab* , c-bd)).
              -- Type-correct without extra transports because (snd q : El (⅀Assoc-C' I J M (fst q)))
              -- is precisely the type expected as the third argument of F (...).
              step2 : F (fst (equivFun (⟦⅀⟧ I J) ab*))
                        (snd (equivFun (⟦⅀⟧ I J) ab*))
                        c-bd
                    ≡ data-NL (equivFun (⅀Assoc≃ I J M) abc)
              step2 i =
                let q = sym (secEq (⟦⅀⟧ (⅀ I J) (⅀Assoc-C' I J M)) (ab* , c-bd)) i
                in F (fst (equivFun (⟦⅀⟧ I J) (fst q)))
                     (snd (equivFun (⟦⅀⟧ I J) (fst q)))
                     (snd q)
          in step1 ∙ step2

        homog : data-NR ≡ data-NL ∘ equivFun (⅀Assoc≃ I J M)
        homog = funExt homog-pt

        path-ua : PathP (λ i → ua (⅀Assoc≃ I J M) i → X) data-NR data-NL
        path-ua = homog ◁ (λ i el → data-NL (ua-unglue (⅀Assoc≃ I J M) i el))

        data-path : PathP (λ i → El (Inj (⅀Assoc≃ I J M) i) → X) data-NR data-NL
        data-path = subst (λ p → PathP (λ i → p i → X) data-NR data-NL)
                          (⟦⅀Assoc⟧ I J M)
                          path-ua

        aux : join O ((join O) <$> (I ▷ k ▷ D)) ≡ join O (join O (I ▷ k ▷ D))
        aux i = Inj (⅀Assoc≃ I J M) i ▷ assoc I J M k ks kss i ▷ data-path i
