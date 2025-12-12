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

    P^ : 𝓟 A
    P^ x = ¬ (x ≡ b) → ¬ P

    DNE-P^ : ¬¬Closed P^
    DNE-P^ x nnP^ = (λ x≠b p → nnP^ λ x∈P^ → ∅ (x∈P^ x≠b p ) )

    cPmin→WEM : (_≡_ {A = A}) isDec → WEM P
    cPmin→WEM eqDec with wfMinDNE P^ DNE-P^ b (λ ¬b=b p → ¬b=b refl)
    ... | (x ,, x≠b→¬P , x∈minP^)
      with eqDec {x} {b}
    ... | in1 yes = in2 (λ ¬p → x∈minP^ a (λ _ p → ¬p p )  (transp (R a) (~ yes) Rab ) )
    ... | in2 no = in1 (x≠b→¬P no )

  data cP (a₀ : A) : 𝓟 A where
    cPmin : ¬¬ P a₀ → ∀ {x} → (∀ y → ¬ R y x) → cP a₀ x
    cPsuc : ∀ {x y} → R y x → cP a₀ x

  wfMinDNE→WN : ∀ x → Σ[ y ∈ A ] (RMin R y × (R ⋆) y x)
  -- wfMinDNE→WN x with wfMinDNE (λ x → ∁∁ ( Σ[ y ∈ A ] (RMin R y × (R ⋆) y x))) (¬¬Closed∁ _) x (λ {x₁ → x₁ {!   !}})
  wfMinDNE→WN x with wfMinDNE (∁∁ (((~R R) ⋆) x)) (¬¬Closed∁ _) x (λ z → z ε⋆)
  ...| (y ,, ¬¬R⋆yx , ymin) = y
    ,,  (λ z Rzy → ymin z (λ H → ¬¬R⋆yx (λ R*xy → H ( R*xy ⋆!⋆ ax⋆ (~R R) Rzy ) ) ) Rzy )
    , {!   !}

  -- This goal has possibly been proved else where: normal forms are not not closed.
  wfMinDNE→decRmin : _≡_ {A = A} isDec → dec (RMin R) -- (EM ∘ RMin R)
  wfMinDNE→decRmin eqDec x with wfMinDNE (∁∁ (((~R R) ⋆) x)) (¬¬Closed∁ _) x (λ z → z ε⋆)
  ...| (y ,, ¬¬R⋆yx , ymin) with eqDec {x} {y}
  ... | in1 yes = in1 (λ z Rzx → ymin z (λ H → H (ax⋆ (~R R) Rzx ) ) (transp (R z) yes Rzx ) )
  ... | in2 no  = in2 (λ H → ¬¬R⋆yx (λ { ε⋆ → no refl ; (Rzx ,⋆ R*yx) → H _ Rzx } ) )

  -- This seems to be false
  -- wfMinDNE→eqDec→∁∁R⊆R : _≡_ {A = A} isDec → (∀ y x → ¬¬ (R y x) → R y x)
  -- wfMinDNE→eqDec→∁∁R⊆R eqDec y x ¬¬Ryx = ?
  --   with wfMinDNE (λ z → (x ≡ z) ⊔ ((z ≡ y) × R z x)) nnPP x (in1 refl)
  --     where nnPP : _
  --           nnPP z ¬z∉P with eqDec {z} {y}
  --           ... | in1 yes = in2 (yes , ∅ (¬z∉P λ {(in1 x=z) → {!   !} ; (in2 (z=y , Rzx)) → ¬¬Ryx {!   !} } ) )
  --           ... | in2 no  = {!   !}
  -- ... | c = {!   !}

  -- Proof idea: let Pz be true if z is x or z is y and Ryx .
  wfMinDNE→eqDec→Rwdec : _≡_ {A = A} isDec → (∁ (~R R)) isDec
  wfMinDNE→eqDec→Rwdec eqDec {x} {y}
    with wfMinDNE (λ z → (z ≡ x) ⊔ ((z ≡ y) × ¬¬ R y x)) nnPP x (in1 refl) where
      nnPP : _
      nnPP z ¬¬Pz with eqDec {z} {x}
      ... | in1 z=x = in1 z=x
      ... | in2 z≠x with eqDec {z} {y}
      ... | in1 z=y = in2 (z=y , λ ¬Ryx → ¬¬Pz (λ { (in1 z=x) → z≠x z=x ;
                                                    (in2 (z=y , ¬¬Ryx)) → ¬¬Ryx ¬Ryx } ) )
      ... | in2 z≠y = ∅ (¬¬Pz λ { (in1 z=x) → z≠x z=x ; (in2 (z=y , ¬¬Ryz)) → z≠y z=y } )
  ... | z ,, in1 z=x , z∈minP = in1 (λ Ryx → z∈minP y (in2 (refl , λ ¬Ryx → ¬Ryx Ryx))
                                                      (transp (R y) (~ z=x) Ryx ) )
  ... | z ,, in2 (z=y , ¬¬Ryx) , z∈minP = in2 ¬¬Ryx

  wfMinDNE→eqDec→∁∁R⊆R→∁RMin⊆ΣR : _≡_ {A = A} isDec
    → (∀ x y → ¬¬ (R y x) → R y x) → ∀ x → ∁RMin⊆ΣR R x
  wfMinDNE→eqDec→∁∁R⊆R→∁RMin⊆ΣR eqDec Ris¬¬Closed x x∉RMin
    with wfMinDNE (((~R R) ʳ) x) nnPP x εʳ
      where nnPP : _
            nnPP y ¬¬Rryx with eqDec {x} {y}
            ... | in1 x=y = transp ((~R R ʳ) x) x=y εʳ
            ... | in2 x≠y = axʳ (Ris¬¬Closed x y (λ ¬Ryx → ¬¬Rryx
                  λ { (axʳ Ryx) → ¬Ryx Ryx ; εʳ → x≠y refl } ))
  ... | y ,, axʳ Ryx , y∈minP = y ,, Ryx
  ... | y ,, εʳ , y∈minP = ∅ (x∉RMin λ y Ryx → y∈minP y (axʳ Ryx ) Ryx )

  wfMinDNE→eqDec→∁∁R⊆R→isMinDec : _≡_ {A = A} isDec → (∀ x y → ¬¬ (R y x) → R y x) → R isMinDec
  wfMinDNE→eqDec→∁∁R⊆R→isMinDec eqDec Ris¬¬Closed x =
    ∁RMin⊆ΣR∩decNF⊆MinDec R x (wfMinDNE→eqDec→∁∁R⊆R→∁RMin⊆ΣR eqDec Ris¬¬Closed x
                            , wfMinDNE→decRmin eqDec x )
