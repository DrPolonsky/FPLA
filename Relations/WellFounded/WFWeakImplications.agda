open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Classical
open import Relations.Decidable
open import Relations.ClosureOperators
open import Relations.Seq
-- TODO: Remove unused imports
module Relations.WellFounded.WFWeakImplications where

open import Relations.WellFounded.WFDefinitions public
open import Relations.WellFounded.WFWeakDefinitions public
open import Relations.WellFounded.WFBasicImplications public
open BasicImplications

module WeakImplications {A : Set} (R : 𝓡 A) where
  -- Implications between weaker well-foundedness notions

  -- Remark.  The converse of this is exactly the DNS for accessibility
  ¬¬isWFacc→isWFacc- :  ¬¬ (R isWFacc) → isWFacc- R
  ¬¬isWFacc→isWFacc- ¬¬wfAccR = λ x ¬accx     → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

  -- The converse of this is exactly the DNS for all inductive φ
  ¬¬isWFind→isWFind- : ¬¬ (R isWFind) → isWFind- R
  ¬¬isWFind→isWFind- ¬¬WFiR   = λ φ φind x ¬φx → ¬¬WFiR (λ isWFiR → ¬φx (isWFiR x φ φind))


  ¬¬isWFseq→isWFseq- : ¬¬ (R isWFseq) → isWFseq- R
  ¬¬isWFseq→isWFseq- ¬¬WFs = λ s sdec  → ¬¬WFs (λ WFs → snd (WFs s) (sdec (fst (WFs s)) ) )

  ¬¬isWFmin→isWFmin- : ¬¬ (R isWFmin) → isWFmin- R
  ¬¬isWFmin→isWFmin- ¬¬WFmR   = λ P p ¬Σ → ¬¬WFmR (λ WFmR → ¬Σ (WFmR P _ p ) )

  isWFminDNE→isWFminDNE- : R isWFminDNE → isWFminDNE- R
  isWFminDNE→isWFminDNE- a b c d e = e (a b c _ d)

  isWFacc-→isWFind- : isWFacc- R → isWFind- R
  isWFacc-→isWFind- RisWFacc- P Pind d ¬Pd = RisWFacc- d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind-→isWFacc- : isWFind- R → isWFacc- R
  isWFind-→isWFacc- RisWFind = RisWFind (λ y → y ∈ R -accessible) (λ x → acc)

  isWFacc-→isWFmin- : isWFacc- R → isWFmin- R
  isWFacc-→isWFmin- RisWFacc- P {d} d∈P ¬Σ₀ = RisWFacc- d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → x ∈ R -accessible → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  -- redundant [AP]
  isWFind-→isWFmin- : isWFind- R → isWFmin- R
  isWFind-→isWFmin- RisWFind- P {d} d∈P =
    let φ : 𝓟 A
        φ x = x ∈ P → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
        φ-ind : R -inductive φ
        φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
      in λ ¬Σ → RisWFind- φ φ-ind d (λ H → H d∈P ¬Σ )

  isWFmin-→isWFseq- : isWFmin- R → isWFseq- R
  isWFmin-→isWFseq- RisWFmin- s s-dec = RisWFmin- B (zero ,, refl) f
    where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
          f : ¬ Σ[ d ∈ A ] (d ∈ R - B -minimal)
          f (d ,, dRBmin) with pr1 dRBmin
          ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                                (transp (R (s (succ n))) sn≡d (s-dec n))

  -- redundant [AP]
  isWFacc-→isWFseq- : isWFacc- R → isWFseq- R
  isWFacc-→isWFseq- RisWFacc- s0 s0-inc =
    RisWFacc- (s0 0) (λ s00∈acc → f (s0 0) s00∈acc s0 s0-inc refl ) where
      f : ∀ x → x ∈ R -accessible → ∀ s → s ∈ R -decreasing → ¬ (s 0 ≡ x)
      f x (acc xacc) s s-inc s0=x =
        f (s 1) (xacc (s 1) (transp (R (s 1)) s0=x (s-inc 0) ) )
          (s ∘ succ) (λ n → s-inc (succ n)) refl

  isWFmin-→isWFminDNE- : isWFmin- R → isWFminDNE- R
  isWFmin-→isWFminDNE- RisWFmin- P  = λ _ → RisWFmin- P

  --  Double check this solution as it went from being long to simple.
  isWFminDNE-→isWFmin- : isWFminDNE- R → isWFmin- R
  isWFminDNE-→isWFmin- RisWFminDNE- P {d} d∈P ¬∃minP with RisWFminDNE- (∁ (∁ P)) (λ x y z → y λ w → w z ) (λ z → z d∈P)
  ... | c = c λ { (x ,, ¬x∉P , H) → ¬x∉P (λ x∈P →
                   ¬∃minP (x ,, x∈P , λ y y∈P Ryx → H y (λ z → z y∈P) Ryx ) )  }

  ¬¬lemma : ∀ (X : Set) (Q : 𝓡 X) (P : 𝓟 X) (a : X) → ¬¬ (Σ[ b ∈ X ] (Q b a × P b) ⊔ (∀ b → Q b a → ¬ P b))
  ¬¬lemma X Q P a ¬⊔ = ¬⊔ (in2 λ b Qba b∈P → ¬⊔ (in1 (b ,, Qba , b∈P) ) )

  ¬¬lemmaA : ∀ (P : 𝓟 A) (a : A) → ¬¬ (Σ[ b ∈ A ] (R b a × P b) ⊔ (∀ b → R b a → ¬ P b))
  ¬¬lemmaA P a ¬⊔ = ¬⊔ (in2 λ b Rba b∈P → ¬⊔ (in1 (b ,, Rba , b∈P) ) )

  ¬¬lemmaC : ∀ (P : 𝓟 A) → (∁ (∁ P) ⊆ P) → (a : A) →
        ¬¬ (    (Σ[ bRba ∈ (Σ[ b ∈ A ] R b a) ] (¬ P (fst bRba)))
             ⊔  (∀ (bRba :  Σ[ b ∈ A ] R b a)    → P (fst bRba)))
  ¬¬lemmaC P CCP⊆P a ¬⊔ = ¬⊔ (in2 λ { (b ,, Rba) → CCP⊆P b (λ b∉P → ¬⊔ (in1 ((b ,, Rba) ,, b∉P ) ) )  } )


  -- April 28th: Are these ToDos still something we want or shall we delete them?
  {-
  To do:
  - WFmin[ind]
  - WFmin[CCind]
  - replace implications WFseq- -> WFacc- and WFDNE- -> WFacc- to use CCaccInd
  - from WFacc and strong decidability of acc (acc∈cored), prove wf[ind]
  -}

  isWFseq-₂ : Set
  isWFseq-₂ = ∀ (s : ℕ → A) → ¬¬ (Σ[ n ∈ ℕ ] (R (s (succ n)) (s n) → ⊥))

  -- Does this require R to be ¬¬ Closed?  ¬¬Rxy → Rxy AKA ∁∁R ⊆ R ??
  -- isWFseq-₂ ↔ isWFseq- R
  -- because ¬¬ (∃ x. P(x)) ↔ ¬ (∀ x. ¬ P(x))


  -- WFseq-₂→WFseq+- : isWFseq-₂ → isWFseq+- R
  -- WFseq-₂→WFseq+- isSeq2 s ¬Ex = {! ¬  !}
  --
  -- -- Will be tougher. Both should be provable.
  -- WFseq-→WFseq+- : isWFseq- R → isWFseq+- R
  -- WFseq-→WFseq+- RisWFseq- s ¬n∈Rmin with RisWFseq- s
  -- ... | c = ¬n∈Rmin {!   !}

  WFseq+-→WFseq- : isWFseq+- R → isWFseq- R
  WFseq+-→WFseq- RisWFseq+- s s-dec = RisWFseq+- (λ _ → s zero) (λ z → snd z (s-dec zero))


open WeakImplications public
