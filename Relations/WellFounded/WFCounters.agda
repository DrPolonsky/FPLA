open import Logic
open import Datatypes
open import Predicates
open import Classical
open import Relations.Core
open import Relations.WellFounded.WFDefinitions
module Relations.WellFounded.WFCounters where
open import Relations.Decidable
open import Relations.ClosureOperators

data _<_ : ℕ → ℕ → Set where
  base< : ∀ {n} → n < succ n
  succ< : ∀ {n m} → n < m → n < succ m

mono< : ∀ {m n} → m < n → succ m < succ n
mono< base< = base<
mono< (succ< mn) = succ< (mono< mn)

zero< : ∀ {m} → zero < succ m
zero< {zero} = base<
zero< {succ m} = succ< zero<

module LTnotWFmin (P : 𝓟 ℕ) where
-- If natural numbers satisfy WFmin, then every predicate on ℕ is decidable

  data Psat (n : ℕ) : 𝓟 ℕ where
    Psat0 : ∀ k → P (add k n) → Psat n k
    PsatS : ∀ k → Psat n (succ k)

  lemma1 : ∀ n k → (_<_ - (Psat n) -minimal) k → k < 2
  lemma1 n zero kmin = succ< base<
  lemma1 n (succ zero) kmin = base<
  lemma1 n (succ (succ k)) (_ , H) = ∅ (H (succ zero) (PsatS zero) (mono< zero< ))

  lemma2 : ∀ n k → (_<_ - (Psat n) -minimal) k → EM (P n)
  lemma2 n k kmin with lemma1 n k kmin
  lemma2 n .1 (Ps1 , ¬Ps0) | base< = in2 (λ pn → ¬Ps0 zero (Psat0 zero pn ) base< )
  lemma2 n .0 (Psat0 .0 p , _) | succ< base< = in1 p

  lemma3 : _<_ isWFmin → dec P
  lemma3 wfmin n with wfmin (Psat n) _ (PsatS zero)
  ... | (k ,, kmin) = lemma2 n k kmin

  lemma4 : _<_ isWFminDNE → ¬¬Closed P → dec P
  lemma4 wfmin₀ ¬¬CP n with wfmin₀ (Psat n) nnCPs _ (PsatS zero)
    where nnCPs : ¬¬Closed (Psat n)
          nnCPs  zero nnp0 = Psat0 0 (¬¬CP n λ pn → nnp0 λ {(Psat0 .0 p) → pn p})
          nnCPs (succ k) _ = PsatS k
  ... | (k ,, kmin) = lemma2 n k kmin

module wfMin→EM (wfMin< : _<_ isWFmin) (P : Set) where
  -- If strict order on natural numbers satisfies isWFmin, then excluded middle holds.
  P∨succ : ℕ → Set
  P∨succ 0 = P
  P∨succ (succ n) = ⊤

  EMP : EM P
  EMP with wfMin< (P∨succ) (succ 0) tt
  ... | zero ,, p , _ = in1 p
  ... | succ n ,, tt , H = in2 (λ p → H 0 p zero<)

module wfMinDNE→WEM (wfMinDNE< : _<_ isWFminDNE) (P : Set) where
-- If natural numbers satisfy WFminDNE, then we get weak excluded middle. (P is ¬P or ¬¬P).
-- This shows that we can't prove in Agda that ℕ and < together satisfy WFminDNE.

  P∨succ : ℕ → Set
  P∨succ 0 = ¬¬ P
  P∨succ (succ n) = ⊤

  WEMP : WEM P
  WEMP with wfMinDNE< (P∨succ)  (λ {zero → λ z np → z (λ nnp → nnp np)
                                  ; (succ x) → λ x → tt }) (succ 0) tt
  ... | zero ,, nnp , _ = in2 nnp
  ... | succ n ,, tt , H = in1 (λ p → H 0 (λ z → z p) zero<)

module isWFminImpliesDec {A : Set} (R : 𝓡 A) (wfMin : R isWFmin) (P : 𝓟 A) where
  -- Here we show that if R is well founded minimality wise, and is non-empty,
  -- then every predicate is decidable.

  RisWFmin→RisDec : R isDec
  RisWFmin→RisDec {x} {y} with wfMin (λ z → (y ≡ z) ⊔ R x y) y (in1 refl)
  ... | z ,, in1 refl , zMin = in2 (λ Rxy → zMin x (in2 Rxy) Rxy)
  ... | z ,, in2 Rxy , zMin = in1 Rxy

  RisWFmin→RisMinDec : R isMinDec
  RisWFmin→RisMinDec x with wfMin (((~R R) ʳ) x) x εʳ
  ... | y ,, axʳ Ryx , ymin = in1 (y ,, Ryx)
  ... | y ,, εʳ , ymin = in2 λ z Rzx → ymin z (axʳ Rzx) Rzx

  data cP (a₀ : A) : 𝓟 A where
      cPmin : P a₀ → ∀ {x} → (∀ y → ¬ R y x) → cP a₀ x
      cPsuc : ∀ {x y} → R y x → cP a₀ x

  cPlemma : ∀ {b c} → R b c → dec P
  cPlemma Rbc a with wfMin (cP a) _ (cPsuc Rbc)
  ... | m ,, cPmin pa _ , mIsMin = in1 pa
  ... | m ,, cPsuc {.m} {y} Rym , mIsMin with RisWFmin→RisMinDec y
  ... | in1 (z ,, Rzy) = ∅ (mIsMin y (cPsuc Rzy) Rym )
  ... | in2 yMin = in2 (λ pa → mIsMin y (cPmin pa yMin) Rym )

  module nonemptyRimpliesEM (a b : A) (Rab : R a b) (P : Set) where

    data P^ : 𝓟 A where
      cPa : P → P^ a
      cPb : P^ b

    cPmin→EM : EM P
    cPmin→EM with wfMin P^ b cPb
    ... | x ,, cPa p , xmin = in1 p
    ... | x ,, cPb , xmin = in2 (λ p → xmin a (cPa p) Rab )

module isWFminDNEImpliesWDec {A : Set} (R : 𝓡 A) (wfMinDNE : R isWFminDNE) (P : 𝓟 A) where
  -- Here we show that if R is WFminDNE and R normal forms are decidable, then every predicate is weakly decidable.

  module nonemptyRimpliesWEM (a b : A) (Rab : R a b) (P : Set) where

    -- data P^ : 𝓟 A where
    --   cPa : P → P^ a
    --   cPb : P^ b

    P^ : 𝓟 A
    P^ x = x ≡ a → ¬¬ P

    cPmin→WEM : (_≡_ {A = A}) isDec → WEM P
    cPmin→WEM Adec with wfMinDNE P^ nncP^ b (λ b=x → {!   !})
      where nncP^ : _
            nncP^ x nnpx q = λ np → nnpx (λ h → h q np )
    ... | (x ,, x=a→nnp , xmin) = case yes no (Adec {x} {a}) where
      yes = λ x=a → in2 (x=a→nnp x=a)
      no = λ x≠a → in1 (λ p → xmin a (λ _ ¬p → ¬p p) {!   !} )


    -- P^ : 𝓟 A
    -- P^ x = ¬ ((x ≡ b → ⊥) × (x ≡ a → P → ⊥))
    --
    -- cPmin→WEM : WEM P
    -- cPmin→WEM with wfMinDNE P^ nncP^ b (λ {(l , r) → l refl})
    --   where nncP^ : _
    --         nncP^ x nnpx q = nnpx (λ p^x → p^x q)
    -- ... | x ,, h , xmin = in2 (λ ¬p → xmin a ((λ {(¬a=b , f) → {!   !} } ))
    --   (∅ (h ((λ x=b → xmin a (λ {(g1 , g2) → {!   !} })
    --         {!   !} ) , {!   !} ) ) ) )

            -- in1 (λ p → xmin a (λ {(l , r) → r refl p })
            --               (∅ (h ((λ x=b → xmin a ((λ {(l , r) → r refl p })) (transp (R a) (~ x=b) Rab ) )
            --                   , λ x=a p → {!   !} ) ) ) )

{-    P^ : 𝓟 A
    P^ x = ¬¬ (x ≡ b) ⊔ ¬ (x ≡ a → P → ⊥)

    cPmin→WEM : WEM P
    cPmin→WEM with wfMinDNE P^ nncP^ b (in1 λ z → z refl)
      where nncP^ : _
            nncP^ x nnpx = in1 (λ x≠b → nnpx λ { (in1 s) → s x≠b ; (in2 r) → {!   !} } )
    ... | x ,, in1 h , xmin = in1 (λ p → h (λ {x=b → xmin a (in2 λ g → g refl p ) (transp (R a) (~ x=b) Rab ) }) )
    ... | x ,, in2 h , xmin = in2 (λ ¬p → h (λ _ p → ¬p p ) )
-}

  data cP (a₀ : A) : 𝓟 A where
    cPmin : ¬¬ P a₀ → ∀ {x} → (∀ y → ¬ R y x) → cP a₀ x
    cPsuc : ∀ {x y} → R y x → cP a₀ x

  wfMinDNE→WN : ∀ x → Σ[ y ∈ A ] (RMin R y × (R ⋆) y x)
  wfMinDNE→WN x with wfMinDNE (λ x → ∁∁ ( Σ[ y ∈ A ] (RMin R y × (R ⋆) y x))) (¬¬Closed∁ _) x (λ {x₁ → x₁ {!   !}})
  ...| z = {!   !}

  wfMinDNE→decRmin : ∀ x → EM (RMin R x) -- (EM ∘ RMin R)
  wfMinDNE→decRmin x with wfMinDNE (RMin R) (λ y → {! ¬¬Closed∁  !}) x -- This goal has possibly been proved else where: normal forms are not not closed.
  ... | z = {!   !}

  wfMinDNE→isMinDec : R isMinDec
  wfMinDNE→isMinDec x = {!   !}

  nncp : ∀ {a} → R isMinDec → ¬¬Closed (cP a)
  nncp dmR x nnx with dmR x
  ... | in1 (z ,, Rzx) = cPsuc Rzx
  ... | in2 xMin = ∅ (nnx (λ {(cPmin nnPa xMin') → nnPa
                            (λ Pa → nnx λ {(cPmin nnPa xMin'') → nnPa (λ Pa → nnPa
                              (λ Pa' → nnx (λ {(cPmin nnPa' xMin'') → xMin {!   !} {!   !}
                                             ; (cPsuc x) → {!   !}})))
                            -- nnPa
                            --   (λ _ →
                            --      nnPa
                            --      (λ z →
                            --         nnx
                            --         (λ z₁ →
                            --            (λ { (cPmin nnPa xMin'')
                            --                   → ?5 (xMin = xMin''') (nnx = (λ z₂ → z₂ z₁)) (nnPa = (λ z₂ → z₂ z))
                            --                     (xMin' = xMin''') (Pa = z) (nnPa = nnPa) (xMin'' = xMin'')
                            --               ; (cPsuc Ryx) → xMin'' y Ryx
                            --               })
                            --            z₁))) -- auto provides a broken solution
                                          ; (cPsuc Ryx) → xMin' _ Ryx})
                            ; (cPsuc Ryx) → xMin _ Ryx}))

  cPlemma : ∀ {b c} → R b c → R isMinDec → wdec P
    -- _isWFminDNE = ∀ (P : 𝓟 A) → ¬¬Closed P → ∀ a → a ∈ P → Σ[ m ∈ A ] _-_-minimal P m
  cPlemma Rbc dmR a with wfMinDNE (cP a) (nncp {a} dmR) _ (cPsuc Rbc)
    where
      nncp2 : ¬¬Closed (cP a)
      nncp2 x nnx with dmR x
      ... | in1 (z ,, Rzx) = cPsuc Rzx
      ... | in2 xMin = ∅ (nnx (λ {(cPmin nnPa xMin') → nnPa
                                (λ Pa → nnx λ {(cPmin nnPa xMin'') → {!   !} -- auto provides a broken solution
                                             ; (cPsuc Ryx) → xMin' _ Ryx})
                                ; (cPsuc Ryx) → xMin _ Ryx}))
  ... | x ,, cPmin nnPa xMin , q = in2 nnPa
  ... | x ,, cPsuc Ryx , q = in1 (λ Pa → q {!   !} (cPmin (λ z → z Pa) {!   !}) Ryx)
