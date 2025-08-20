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
  ¬¬isWFacc→isWFacc¬¬ :  ¬¬ (R isWFacc) → R isWFacc¬¬
  ¬¬isWFacc→isWFacc¬¬ ¬¬wfAccR = λ x ¬accx     → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

  -- The converse of this is exactly the DNS for all inductive φ
  ¬¬isWFind→isWFind¬¬ : ¬¬ (R isWFind) → R isWFind¬¬ 
  ¬¬isWFind→isWFind¬¬ ¬¬WFiR   = λ φ φind x ¬φx → ¬¬WFiR (λ isWFiR → ¬φx (isWFiR x φ φind))


  ¬¬isWFseq→isWFseq- : ¬¬ (R isWFseq) → isWFseq- R
  ¬¬isWFseq→isWFseq- ¬¬WFs = λ s sdec  → ¬¬WFs (λ WFs → snd (WFs s) (sdec (fst (WFs s)) ) )

  ¬¬isWFmin→isWFmin- : ¬¬ (R isWFmin) → isWFmin- R
  ¬¬isWFmin→isWFmin- ¬¬WFmR   = λ P p ¬Σ → ¬¬WFmR (λ WFmR → ¬Σ (WFmR P _ p ) )

  isWFminDNE→isWFminDNE- : R isWFminDNE → isWFminDNE- R
  isWFminDNE→isWFminDNE- a b c d e = e (a b c _ d)

  isWFacc¬¬→isWFind¬¬ : R isWFacc¬¬ → R isWFind¬¬ 
  isWFacc¬¬→isWFind¬¬ RisWFacc¬¬ P Pind d ¬Pd = RisWFacc¬¬ d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind¬¬→isWFacc¬¬ : R isWFind¬¬  → R isWFacc¬¬
  isWFind¬¬→isWFacc¬¬ RisWFind = RisWFind (λ y → y ∈ R -accessible) (λ x → acc)

  isWFacc¬¬→isWFmin- : R isWFacc¬¬ → isWFmin- R
  isWFacc¬¬→isWFmin- RisWFacc¬¬ P {d} d∈P ¬Σ₀ = RisWFacc¬¬ d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → x ∈ R -accessible → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  -- redundant [AP]
  isWFind¬¬→isWFmin- : R isWFind¬¬  → isWFmin- R
  isWFind¬¬→isWFmin- RisWFind¬¬ P {d} d∈P =
    let φ : 𝓟 A
        φ x = x ∈ P → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
        φ-ind : R -inductive φ
        φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
      in λ ¬Σ → RisWFind¬¬ φ φ-ind d (λ H → H d∈P ¬Σ )

  isWFmin-→isWFseq- : isWFmin- R → isWFseq- R
  isWFmin-→isWFseq- RisWFmin- s s-dec = RisWFmin- B (zero ,, refl) f
    where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
          f : ¬ Σ[ d ∈ A ] (d ∈ R - B -minimal)
          f (d ,, dRBmin) with pr1 dRBmin
          ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                                (transp (R (s (succ n))) sn≡d (s-dec n))

  -- redundant [AP]
  isWFacc¬¬→isWFseq- : R isWFacc¬¬ → isWFseq- R
  isWFacc¬¬→isWFseq- RisWFacc¬¬ s0 s0-inc =
    RisWFacc¬¬ (s0 0) (λ s00∈acc → f (s0 0) s00∈acc s0 s0-inc refl ) where
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

open import Relations.FinitelyBranching
module FBImplications {A : Set} {R : 𝓡 A} (RisFB : (~R R) isFB) where

  -- May 2nd note: This must exist somewhere in general form?
  RisWF→¬¬RisWF : ∀ {a} → (R -accessible) a → ¬ (¬ (R -accessible) a)
  RisWF→¬¬RisWF RisWF ¬RisWF = ∅ (¬RisWF RisWF)

  -- REF: Move to WFWeakDefinitions?
  FB→isWFminDNE-→isWFacc¬¬ : isWFminDNE- R → R isWFacc¬¬
  FB→isWFminDNE-→isWFacc¬¬ RisWF x₀ x₀∉acc =
    RisWF (∁ (R -accessible)) (λ a nnnac ac → ∅ (nnnac (RisWF→¬¬RisWF ac))) x₀∉acc f
      where f : ¬ Σ-syntax A (R - ∁ (R -accessible)-minimal)
            f (z ,, z∉acc , z∈min) =
              FB→DNS (~R R) (R -accessible) z (RisFB z)
                     (λ y Ryx y∉acc → z∈min y y∉acc Ryx )
                     λ za → z∉acc (acc za)

-- Should this be a seperate module, if so what name?
module CoreductiveImplications {A : Set} (R : 𝓡 A) where
  open import Relations.Coreductive R

  isWFminCor→Cor¬¬ : isWFminCor R → ∀ (P : 𝓟 A) → R -coreductive P → ∀ x → ¬¬ P x
  isWFminCor→Cor¬¬ iwfc P Pco x ¬px with iwfc P Pco ¬px
  ... | (y ,, ¬py , ymin) with Pco y ¬py
  ... | (z ,, Rzy , ¬pz) = ymin z ¬pz Rzy

  Cor¬¬→isWFminCor : (∀ P → R -coreductive P → ∀ x → ¬¬ P x) → isWFminCor R
  Cor¬¬→isWFminCor H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFcor→isWFminCor : R isWFcor  → isWFminCor R
  isWFcor→isWFminCor RisWFcor = Cor¬¬→isWFminCor (λ P P∈Cor a → λ a∉P → a∉P (RisWFcor a P P∈Cor))  

  isWFminCor+→isWFminCor : isWFminCor+ R → isWFminCor R
  isWFminCor+→isWFminCor RisWFminCor+ P Pcor a∉P with RisWFminCor+ P Pcor a∉P
  ... | (x ,, x∉P , H) = x ,, x∉P , λ y y∉P Ryx → y∉P (H y Ryx)

  Cor¬¬→isWFminCor+ : (∀ P → R -coreductive P → ∀ x → ¬¬ P x) → isWFminCor+ R
  Cor¬¬→isWFminCor+ H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFminCor→isWFminCor+ : isWFminCor R → isWFminCor+ R
  isWFminCor→isWFminCor+ wfmc = Cor¬¬→isWFminCor+ (isWFminCor→Cor¬¬ wfmc )

  isWFminDNE→isWFminCor+ : R isWFminDNE → isWFminCor+ R
  isWFminDNE→isWFminCor+ RisWFminDNE P Pco {a} a∉P
    with  RisWFminDNE (∁ P) DNS¬ a a∉P
    where DNS¬ = λ x ¬Px ¬¬Px → ¬Px (λ z → z ¬¬Px)
  ... | (y ,, ¬Py , ymin) with Pco y ¬Py
  ... | (z ,, Rzy , ¬Pz) = ∅ (ymin z ¬Pz Rzy)

  isWFminDNE→Cor¬¬ : R isWFminDNE → ∀ P → R -coreductive P → ∀ a → ¬¬ P a
  isWFminDNE→Cor¬¬ RisWFmin = isWFminCor→Cor¬¬
    (isWFminCor+→isWFminCor (isWFminDNE→isWFminCor+  RisWFmin))

  isWFminDNE-→Cor¬¬ : isWFminDNE- R → ∀ P → R -coreductive P → ∀ a → ¬¬ P a
  isWFminDNE-→Cor¬¬ WFR P Pcor a a∉P = WFR (∁ P) (λ x z z₁ → z (λ z₂ → z₂ z₁)) a∉P f
    where f : _
          f (m ,, m∉P , mmin) with Pcor m m∉P
          ... | (n ,, Rnm , n∉P) = mmin n (λ _ → mmin n n∉P Rnm) Rnm

  -- This implication also follows from isWFminDNE-→isWFmin-→isWFseq-→isWFaccc- (with accCor)
  accCor∧isWFminDNE-→isWFacc¬¬ : R -coreductive (R -accessible) → isWFminDNE- R → R isWFacc¬¬
  accCor∧isWFminDNE-→isWFacc¬¬ accCor RisWF = isWFminDNE-→Cor¬¬ RisWF (R -accessible) accCor

  -- A Noteworthy Consequence
  accCorec→isWFseq-→isWFacc¬¬ : R -coreductive (R -accessible) → isWFseq- R → R isWFacc¬¬
  accCorec→isWFseq-→isWFacc¬¬ AccisCor RisWFseq- a a∉acc = RisWFseq- seq seq-inc  where
    open CorSequence (CS {R -accessible} {AccisCor} (a ,, a∉acc))


  isWFseq-→isWFminCor+ : isWFseq- R → isWFminCor+ R
  isWFseq-→isWFminCor+ RisWFseq P CI {a} ¬pa =  ∅ (RisWFseq seq seq-inc) where
    open CorSequence (CS {P} {CI} (a ,, ¬pa))

  -- The converse is not provable,
  -- because the complement of the image of a sequence is not coreductive (at least not constructively).

  accCorec→isWFminCor+→isWFacc¬¬ : R -coreductive (R -accessible) → isWFminCor+ R → R isWFacc¬¬
  accCorec→isWFminCor+→isWFacc¬¬ acc∈Cor WFmc a a∉acc
    with WFmc (R -accessible) acc∈Cor a∉acc
  ... | (m ,, m∉acc , p) = m∉acc (acc p)

  cor→seqLemma : MP≡ → (s : ℕ → A) → s ∈ (R -decreasing) → R -coreductive (λ a → ¬ Σ-syntax ℕ (λ k → s k ≡ a))
  cor→seqLemma mp≡ s s-inc x ¬¬x∈s with mp≡ s x ¬¬x∈s
  ... | k ,, sk≡x = (s (succ k)) ,, transp (R (s (succ k))) sk≡x (s-inc (k)) ,
     λ ¬∃n → ¬∃n ((succ k) ,, refl)   

  isWFminCor→isWFseq- : MP≡ → isWFminCor R → isWFseq- R
  isWFminCor→isWFseq- mp≡ wfmc s s-inc =
    isWFminCor→Cor¬¬ wfmc (λ a → ¬ Σ[ k ∈ ℕ ] (s k ≡ a) )
                    (cor→seqLemma mp≡ s s-inc) (s zero)
                    λ ¬Ex → ¬Ex ((0 ,, refl ))