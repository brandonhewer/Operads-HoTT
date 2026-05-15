{-# OPTIONS --cubical #-}
-- ============================================================================
-- HoTTOperads.Operad.Endo
--
-- The endomorphism operad `Endo 𝒰 X` on an h-set `X`. Operations at code `A`
-- are functions `(El A → X) → X`; the unit is evaluation at the unique
-- argument of `El 𝜏`; composition is function composition. The three
-- operadic laws are discharged by `subst` over the universe coherences
-- (⟦⅀Idl⟧, ⟦⅀Idr⟧, ⟦⅀Assoc⟧) plus the `ua→→inv` lemma in
-- src/HoTTOperads/UA.agda.
--
-- Formalises from the paper:
--   Definition 7.3 (Section 7, Category of Operads) — `Endo 𝒰 X`.
-- ============================================================================
module HoTTOperads.Operad.Endo where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Univalence
open import Cubical.Data.Unit using (Unit ; tt)

open import HoTTOperads.Universe.Base
open import HoTTOperads.Operad.Base
open import HoTTOperads.UA

private
  variable
    ℓc ℓe ℓ : Level

module _ {ℓc ℓe : Level} (𝒰 : Universe ℓc ℓe) {X : Type ℓ} (isSetX : isSet X) where
  open Universe 𝒰

  -- Operations of the endomorphism operad: n-ary-like functions (El A → X) → X.
  EndoOps : Code → Type (ℓ-max ℓe ℓ)
  EndoOps A = (El A → X) → X

  opaque
    isSetEndoOps : (A : Code) → isSet (EndoOps A)
    isSetEndoOps A = isSetΠ (λ _ → isSetX)

  -- Unit: extract the unique element from a unit-indexed function.
  Endo-id : EndoOps 𝜏
  Endo-id f = f (invEq ⟦𝜏⟧ tt)

  -- Composition: plug n input operations into an n-ary output operation.
  Endo-comp : (A : Code) (B : El A → Code)
            → EndoOps A → ((a : El A) → EndoOps (B a)) → EndoOps (⅀ A B)
  Endo-comp A B f fs xs = f (λ a → fs a (λ b → xs (invEq (⟦⅀⟧ A B) (a , b))))

  opaque
    -- Left-identity law for Endo.
    Endo-idl : (A : Code) (k : EndoOps A)
             → PathP (λ i → EndoOps (Inj (⅀Idl≃ A) i))
                     (Endo-comp 𝜏 (λ _ → A) Endo-id (λ _ → k)) k
    Endo-idl A k =
      subst (λ p → PathP (λ i → (p i → X) → X) lhs k) (⟦⅀Idl⟧ A) path-ua
      where
        lhs : EndoOps (⅀ 𝜏 (λ _ → A))
        lhs = Endo-comp 𝜏 (λ _ → A) Endo-id (λ _ → k)
        lhs-eq : lhs ≡ (λ xs → k (xs ∘ invEq (⅀Idl≃ A)))
        lhs-eq = funExt (λ xs → cong k (funExt (λ b → cong xs (invEq-⅀Idl A b))))
        path-ua : PathP (λ i → (ua (⅀Idl≃ A) i → X) → X) lhs k
        path-ua = lhs-eq ◁ ua→→inv (⅀Idl≃ A) k

    -- Right-identity law for Endo.
    Endo-idr : (A : Code) (k : EndoOps A)
             → PathP (λ i → EndoOps (Inj (⅀Idr≃ A) i))
                     (Endo-comp A (λ _ → 𝜏) k (λ _ → Endo-id)) k
    Endo-idr A k =
      subst (λ p → PathP (λ i → (p i → X) → X) lhs k) (⟦⅀Idr⟧ A) path-ua
      where
        lhs : EndoOps (⅀ A (λ _ → 𝜏))
        lhs = Endo-comp A (λ _ → 𝜏) k (λ _ → Endo-id)
        lhs-eq : lhs ≡ (λ xs → k (xs ∘ invEq (⅀Idr≃ A)))
        lhs-eq = funExt (λ xs → cong k (funExt (λ a → cong xs (invEq-⅀Idr A a))))
        path-ua : PathP (λ i → (ua (⅀Idr≃ A) i → X) → X) lhs k
        path-ua = lhs-eq ◁ ua→→inv (⅀Idr≃ A) k

    -- Associativity law for Endo. See assoc-cell below for the pointwise step
    -- combining secEq on (⟦⅀⟧ A B) (which identifies eq.ab with (a,b)) and on
    -- (⟦⅀⟧ (⅀ A B) …) (which lets us replace the abstract invEq (⅀Assoc≃) with
    -- the explicit composite form on the right-hand side).
    Endo-assoc : (A : Code) (B : El A → Code)
                 (C : (a : El A) → El (B a) → Code)
                 (k : EndoOps A) (ks : (a : El A) → EndoOps (B a))
                 (kss : (a : El A) (b : El (B a)) → EndoOps (C a b))
               → PathP (λ i → EndoOps (Inj (⅀Assoc≃ A B C) i))
                       (Endo-comp A (λ a → ⅀ (B a) (C a)) k
                                  (λ a → Endo-comp (B a) (C a) (ks a) (kss a)))
                       (Endo-comp (⅀ A B) (⅀Assoc-C' A B C)
                                  (Endo-comp A B k ks)
                                  (λ ab → kss (fst (equivFun (⟦⅀⟧ A B) ab))
                                              (snd (equivFun (⟦⅀⟧ A B) ab))))
    Endo-assoc A B C k ks kss =
      subst (λ p → PathP (λ i → (p i → X) → X) lhs rhs) (⟦⅀Assoc⟧ A B C) path-ua
      where
        lhs : EndoOps (⅀ A (λ a → ⅀ (B a) (C a)))
        lhs = Endo-comp A (λ a → ⅀ (B a) (C a)) k
                        (λ a → Endo-comp (B a) (C a) (ks a) (kss a))
        rhs : EndoOps (⅀ (⅀ A B) (⅀Assoc-C' A B C))
        rhs = Endo-comp (⅀ A B) (⅀Assoc-C' A B C)
                        (Endo-comp A B k ks)
                        (λ ab → kss (fst (equivFun (⟦⅀⟧ A B) ab))
                                    (snd (equivFun (⟦⅀⟧ A B) ab)))

        -- For each fixed xs, a, b: a path between lhs's per-(a,b) contribution
        -- and the result of (rhs ∘ precomp by invEq (⅀Assoc≃ A B C)) at (a,b).
        -- We build it in two stages:
        --   step1 : kss a b … ≡ kss (fst eq.ab) (snd eq.ab) (…explicit Q1 form…)
        --     where the interpolation along sym (secEq (⟦⅀⟧ A B) (a,b)) sweeps
        --     (a,b) into eq.ab through the dependent (kss …) and Q.
        --   step2 : (…explicit Q1 form…) ≡ (…abstract invEq (⅀Assoc≃) form…)
        --     where the interpolation along sym (secEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C') …))
        --     replaces σ in invEq (⅀Assoc≃) by (eq.ab', c).
        assoc-cell :
          (xs : El (⅀ A (λ a → ⅀ (B a) (C a))) → X)
          (a : El A) (b : El (B a))
          → kss a b (λ c → xs (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                      (a , invEq (⟦⅀⟧ (B a) (C a)) (b , c))))
          ≡ kss (fst (equivFun (⟦⅀⟧ A B) (invEq (⟦⅀⟧ A B) (a , b))))
                (snd (equivFun (⟦⅀⟧ A B) (invEq (⟦⅀⟧ A B) (a , b))))
                (λ c → xs (invEq (⅀Assoc≃ A B C)
                            (invEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C))
                                   (invEq (⟦⅀⟧ A B) (a , b) , c))))
        assoc-cell xs a b = step1 ∙ step2
          where
            ab' : El (⅀ A B)
            ab' = invEq (⟦⅀⟧ A B) (a , b)

            -- r : (a,b) ≡ eq.ab in Σ (El A) (λ a' → El (B a'))
            r : Path (Σ[ a' ∈ El A ] El (B a'))
                     (a , b)
                     (equivFun (⟦⅀⟧ A B) ab')
            r = sym (secEq (⟦⅀⟧ A B) (a , b))

            -- Stage 1: explicit interpolation of the kss-applied form.
            step1 : kss a b (λ c → xs (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                         (a , invEq (⟦⅀⟧ (B a) (C a)) (b , c))))
                  ≡ kss (fst (equivFun (⟦⅀⟧ A B) ab'))
                        (snd (equivFun (⟦⅀⟧ A B) ab'))
                        (λ c → xs (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                     (fst (equivFun (⟦⅀⟧ A B) ab') ,
                                      invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) ab')))
                                                 (C (fst (equivFun (⟦⅀⟧ A B) ab'))))
                                            (snd (equivFun (⟦⅀⟧ A B) ab') , c))))
            step1 i = kss (fst (r i)) (snd (r i))
                          (λ c → xs (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                       (fst (r i) ,
                                        invEq (⟦⅀⟧ (B (fst (r i))) (C (fst (r i))))
                                              (snd (r i) , c))))

            -- s : (ab' , c) ≡ equivFun (⟦⅀⟧ (⅀ A B) …) (invEq (⟦⅀⟧ (⅀ A B) …) (ab' , c))
            -- in the Σ over El (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)).
            -- This lets us replace σ in the unfolded invEq (⅀Assoc≃ …) by (ab' , c).
            -- Stage 2: replace the explicit form by the abstract invEq (⅀Assoc≃ A B C).
            step2 : kss (fst (equivFun (⟦⅀⟧ A B) ab'))
                         (snd (equivFun (⟦⅀⟧ A B) ab'))
                         (λ c → xs (invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                      (fst (equivFun (⟦⅀⟧ A B) ab') ,
                                       invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) ab')))
                                                  (C (fst (equivFun (⟦⅀⟧ A B) ab'))))
                                             (snd (equivFun (⟦⅀⟧ A B) ab') , c))))
                  ≡ kss (fst (equivFun (⟦⅀⟧ A B) ab'))
                         (snd (equivFun (⟦⅀⟧ A B) ab'))
                         (λ c → xs (invEq (⅀Assoc≃ A B C)
                                      (invEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C))
                                             (ab' , c))))
            step2 i = kss (fst (equivFun (⟦⅀⟧ A B) ab'))
                           (snd (equivFun (⟦⅀⟧ A B) ab'))
                           (λ c → xs (
                             let s = sym (secEq (⟦⅀⟧ (⅀ A B) (⅀Assoc-C' A B C)) (ab' , c))
                             in invEq (⟦⅀⟧ A (λ a → ⅀ (B a) (C a)))
                                      (fst (equivFun (⟦⅀⟧ A B) (fst (s i))) ,
                                       invEq (⟦⅀⟧ (B (fst (equivFun (⟦⅀⟧ A B) (fst (s i)))))
                                                  (C (fst (equivFun (⟦⅀⟧ A B) (fst (s i))))))
                                             (snd (equivFun (⟦⅀⟧ A B) (fst (s i))) ,
                                              snd (s i)))))

        lhs-eq : lhs ≡ (λ xs → rhs (xs ∘ invEq (⅀Assoc≃ A B C)))
        lhs-eq = funExt (λ xs → cong k (funExt (λ a →
                   cong (ks a) (funExt (λ b → assoc-cell xs a b)))))

        path-ua : PathP (λ i → (ua (⅀Assoc≃ A B C) i → X) → X) lhs rhs
        path-ua = lhs-eq ◁ ua→→inv (⅀Assoc≃ A B C) rhs

  -- Definition 7.3 (Section 7, Category of Operads).
  -- The endomorphism operad on `X` packaged as an `Operad 𝒰 EndoOps`.
  Endo : Operad 𝒰 EndoOps
  Operad.isSetK Endo = isSetEndoOps
  Operad.id     Endo = Endo-id
  Operad.compₒ  Endo = Endo-comp
  Operad.idl    Endo = Endo-idl
  Operad.idr    Endo = Endo-idr
  Operad.assoc  Endo = Endo-assoc
