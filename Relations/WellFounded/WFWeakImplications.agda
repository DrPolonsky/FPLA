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
open ConstructiveImplications

module WFx→¬¬WFxImplications {A : Set} (R : 𝓡 A) where 
  doubleNegIntro : ∀ {A : Set} → A → ¬¬ A 
  doubleNegIntro x nx = nx x

  isWFacc→¬¬isWFacc : R isWF → ¬¬ (R isWF)
  isWFacc→¬¬isWFacc RisWF  = doubleNegIntro RisWF  

  -- Implications between weaker well-foundedness notions
module ¬¬WFx→WFx¬¬Implications {A : Set} (R : 𝓡 A) where
  -- Remark.  The converse of this is exactly the DNS for accessibility
  ¬¬isWFacc→isWFacc¬¬ :  ¬¬ (R isWFacc) → R isWFacc¬¬
  ¬¬isWFacc→isWFacc¬¬ ¬¬wfAccR = λ x ¬accx     → ¬¬wfAccR (λ isWFacc → ¬accx (isWFacc x) )

  -- The converse of this is exactly the DNS for all inductive φ
  ¬¬isWFind→isWFind¬¬ : ¬¬ (R isWFind) → R isWFind¬¬ 
  ¬¬isWFind→isWFind¬¬ ¬¬WFiR   = λ φ φind x ¬φx → ¬¬WFiR (λ isWFiR → ¬φx (isWFiR x φ φind))

  ¬¬isWFseq→isWFseq- : ¬¬ (R isWFseq) → R isWFseq-
  ¬¬isWFseq→isWFseq- ¬¬WFs = λ s sdec  → ¬¬WFs (λ WFs → snd (WFs s) (sdec (fst (WFs s)) ) )

  ¬¬isWFmin→isWFmin¬¬ : ¬¬ (R isWFmin) → R isWFmin¬¬
  ¬¬isWFmin→isWFmin¬¬ ¬¬WFmR   = λ P p ¬Σ → ¬¬WFmR (λ WFmR → ¬Σ (WFmR P _ p ) )

module WeakConstructiveImplications {A : Set} (R : 𝓡 A) where
  isWFminDNE→isWFminDNE¬¬ : R isWFminDNE → R isWFminDNE¬¬
  isWFminDNE→isWFminDNE¬¬ a b c d e = e (a b c _ d)

  isWFacc¬¬→isWFind¬¬ : R isWFacc¬¬ → R isWFind¬¬ 
  isWFacc¬¬→isWFind¬¬ RisWFacc¬¬ P Pind d ¬Pd = RisWFacc¬¬ d (λ disRacc → ¬Pd (acc⊆ind P Pind d disRacc) )

  isWFind¬¬→isWFacc¬¬ : R isWFind¬¬  → R isWFacc¬¬
  isWFind¬¬→isWFacc¬¬ RisWFind = RisWFind (λ y → y ∈ R -accessible) (λ x → acc)

  isWFacc¬¬→isWFmin¬¬ : R isWFacc¬¬ → R isWFmin¬¬
  isWFacc¬¬→isWFmin¬¬ RisWFacc¬¬ P {d} d∈P ¬Σ₀ = RisWFacc¬¬ d (λ dRacc → f d d∈P dRacc ¬Σ₀)
    where f : ∀ x → x ∈ P → x ∈ R -accessible → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
          f x x∈P (acc xac) ¬Σ = ¬Σ (x ,, x∈P , (λ y y∈P Ryx → f y y∈P (xac y Ryx) ¬Σ))

  -- redundant [AP]
  isWFind¬¬→isWFmin¬¬ : R isWFind¬¬  → R isWFmin¬¬
  isWFind¬¬→isWFmin¬¬ RisWFind¬¬ P {d} d∈P =
    let φ : 𝓟 A
        φ x = x ∈ P → ¬¬ Σ[ y ∈ A ] (y ∈ R - P -minimal)
        φ-ind : R -inductive φ
        φ-ind x IH x∈P ¬Σ = ¬Σ (x ,, x∈P , λ y y∈P Ryx → IH y Ryx y∈P ¬Σ )
      in λ ¬Σ → RisWFind¬¬ φ φ-ind d (λ H → H d∈P ¬Σ )

  isWFmin¬¬→isWFseq- : R isWFmin¬¬ → R isWFseq-
  isWFmin¬¬→isWFseq- RisWFmin¬¬ s s-dec = RisWFmin¬¬ B (zero ,, refl) f
    where B = (λ d → Σ[ n ∈ ℕ ] (s n ≡ d))
          f : ¬ Σ[ d ∈ A ] (d ∈ R - B -minimal)
          f (d ,, dRBmin) with pr1 dRBmin
          ... | n ,, sn≡d = pr2 dRBmin (s (succ n)) (succ n ,, refl)
                                (transp (R (s (succ n))) sn≡d (s-dec n))

  -- redundant [AP]
  isWFacc¬¬→isWFseq- : R isWFacc¬¬ → R isWFseq-
  isWFacc¬¬→isWFseq- RisWFacc¬¬ s0 s0-inc =
    RisWFacc¬¬ (s0 0) (λ s00∈acc → f (s0 0) s00∈acc s0 s0-inc refl ) where
      f : ∀ x → x ∈ R -accessible → ∀ s → s ∈ R -decreasing → ¬ (s 0 ≡ x)
      f x (acc xacc) s s-inc s0=x =
        f (s 1) (xacc (s 1) (transp (R (s 1)) s0=x (s-inc 0) ) )
          (s ∘ succ) (λ n → s-inc (succ n)) refl

  isWFmin¬¬→isWFminDNE¬¬ : R isWFmin¬¬ → R isWFminDNE¬¬
  isWFmin¬¬→isWFminDNE¬¬ RisWFmin¬¬ P  = λ _ → RisWFmin¬¬ P

  isWFminDNE¬¬→isWFmin¬¬ : R isWFminDNE¬¬ → R isWFmin¬¬
  isWFminDNE¬¬→isWFmin¬¬ RisWFminDNE¬¬ P {d} d∈P ¬∃minP with RisWFminDNE¬¬ (∁ (∁ P)) (λ x y z → y λ w → w z ) (λ z → z d∈P)
  ... | c = c λ { (x ,, ¬x∉P , H) → ¬x∉P (λ x∈P →
                   ¬∃minP (x ,, x∈P , λ y y∈P Ryx → H y (λ z → z y∈P) Ryx ) )  }
  -- April 28th: Are these ToDos still something we want or shall we delete them?
  {-
  To do:
  - WFmin[ind]
  - WFmin[CCind]
  - replace implications WFseq- -> WFacc- and WFDNE- -> WFacc- to use CCaccInd
  - from WFacc and strong decidability of acc (acc∈cored), prove wf[ind]
  -}

  -- WFseq-₂→WFseq+- : isWFseq-₂ → R isWFseq+-
  -- WFseq-₂→WFseq+- isSeq2 s ¬Ex = {! ¬  !}
  --
  -- -- Will be tougher. Both should be provable.
  -- WFseq-→WFseq+- : R isWFseq- → R isWFseq+-
  -- WFseq-→WFseq+- RisWFseq- s ¬n∈Rmin with RisWFseq- s
  -- ... | c = ¬n∈Rmin {!   !}

open WeakConstructiveImplications public

open import Relations.FinitelyBranching
module FBWeakImplications {A : Set} {R : 𝓡 A} (RisFB : (~R R) isFB) where
  FB→isWFminDNE¬¬→isWFacc¬¬ : R isWFminDNE¬¬ → R isWFacc¬¬
  FB→isWFminDNE¬¬→isWFacc¬¬ RisWF x₀ x₀∉acc =
    RisWF (∁ (R -accessible)) (λ a nnnac ac → ∅ (nnnac (RisWF→¬¬RisWF ac))) x₀∉acc f
      where f : ¬ Σ-syntax A (R - ∁ (R -accessible)-minimal)
            f (z ,, z∉acc , z∈min) =
              FB→DNS (~R R) (R -accessible) z (RisFB z)
                     (λ y Ryx y∉acc → z∈min y y∉acc Ryx )
                     λ za → z∉acc (acc za)

module CoreductiveWeakImplications {A : Set} (R : 𝓡 A) where
  open import Relations.Coreductive R

  isWFminCor→Cor¬¬ : R isWFminCor → ∀ (P : 𝓟 A) → R -coreductive P → ∀ x → ¬¬ P x
  isWFminCor→Cor¬¬ iwfc P Pco x ¬px with iwfc P Pco ¬px
  ... | (y ,, ¬py , ymin) with Pco y ¬py
  ... | (z ,, Rzy , ¬pz) = ymin z ¬pz Rzy

  Cor¬¬→isWFminCor : (∀ P → R -coreductive P → ∀ x → ¬¬ P x) → R isWFminCor
  Cor¬¬→isWFminCor H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFcor→isWFminCor : R isWFcor  → R isWFminCor
  isWFcor→isWFminCor RisWFcor = Cor¬¬→isWFminCor (λ P P∈Cor a → λ a∉P → a∉P (RisWFcor a P P∈Cor))  

  isWFminCor+→isWFminCor : R isWFminCor+ → R isWFminCor
  isWFminCor+→isWFminCor RisWFminCor+ P Pcor a∉P with RisWFminCor+ P Pcor a∉P
  ... | (x ,, x∉P , H) = x ,, x∉P , λ y y∉P Ryx → y∉P (H y Ryx)

  Cor¬¬→isWFminCor+ : (∀ P → R -coreductive P → ∀ x → ¬¬ P x) → R isWFminCor+
  Cor¬¬→isWFminCor+ H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFminCor→isWFminCor+ : R isWFminCor → R isWFminCor+
  isWFminCor→isWFminCor+ wfmc = Cor¬¬→isWFminCor+ (isWFminCor→Cor¬¬ wfmc )

  isWFminDNE→isWFminCor+ : R isWFminDNE → R isWFminCor+
  isWFminDNE→isWFminCor+ RisWFminDNE P Pco {a} a∉P
    with  RisWFminDNE (∁ P) DNS¬ a a∉P
    where DNS¬ = λ x ¬Px ¬¬Px → ¬Px (λ z → z ¬¬Px)
  ... | (y ,, ¬Py , ymin) with Pco y ¬Py
  ... | (z ,, Rzy , ¬Pz) = ∅ (ymin z ¬Pz Rzy)

  isWFminDNE→Cor¬¬ : R isWFminDNE → ∀ P → R -coreductive P → ∀ a → ¬¬ P a
  isWFminDNE→Cor¬¬ RisWFmin = isWFminCor→Cor¬¬
    (isWFminCor+→isWFminCor (isWFminDNE→isWFminCor+  RisWFmin))

  isWFminDNE¬¬→Cor¬¬ : R isWFminDNE¬¬ → ∀ P → R -coreductive P → ∀ a → ¬¬ P a
  isWFminDNE¬¬→Cor¬¬ WFR P Pcor a a∉P = WFR (∁ P) (λ x z z₁ → z (λ z₂ → z₂ z₁)) a∉P f
    where f : _
          f (m ,, m∉P , mmin) with Pcor m m∉P
          ... | (n ,, Rnm , n∉P) = mmin n (λ _ → mmin n n∉P Rnm) Rnm

  -- This implication also follows from isWFminDNE¬¬→isWFmin¬¬→isWFseq-→isWFaccc- (with accCor)
  accCor∧isWFminDNE¬¬→isWFacc¬¬ : R -coreductive (R -accessible) → R isWFminDNE¬¬ → R isWFacc¬¬
  accCor∧isWFminDNE¬¬→isWFacc¬¬ accCor RisWF = isWFminDNE¬¬→Cor¬¬ RisWF (R -accessible) accCor

  -- A Noteworthy Consequence
  accCorec→isWFseq-→isWFacc¬¬ : R -coreductive (R -accessible) → R isWFseq- → R isWFacc¬¬
  accCorec→isWFseq-→isWFacc¬¬ AccisCor RisWFseq- a a∉acc = RisWFseq- seq seq-inc  where
    open CorSequence (CS {R -accessible} {AccisCor} (a ,, a∉acc))


  isWFseq-→isWFminCor+ : R isWFseq- → R isWFminCor+
  isWFseq-→isWFminCor+ RisWFseq P CI {a} ¬pa =  ∅ (RisWFseq seq seq-inc) where
    open CorSequence (CS {P} {CI} (a ,, ¬pa))

  -- The converse is not provable,
  -- because the complement of the image of a sequence is not coreductive (at least not constructively).

  accCorec→isWFminCor+→isWFacc¬¬ : R -coreductive (R -accessible) → R isWFminCor+ → R isWFacc¬¬
  accCorec→isWFminCor+→isWFacc¬¬ acc∈Cor WFmc a a∉acc
    with WFmc (R -accessible) acc∈Cor a∉acc
  ... | (m ,, m∉acc , p) = m∉acc (acc p)

  cor→seqLemma : MP≡ → (s : ℕ → A) → s ∈ (R -decreasing) → R -coreductive (λ a → ¬ Σ-syntax ℕ (λ k → s k ≡ a))
  cor→seqLemma mp≡ s s-inc x ¬¬x∈s with mp≡ s x ¬¬x∈s
  ... | k ,, sk≡x = (s (succ k)) ,, transp (R (s (succ k))) sk≡x (s-inc (k)) ,
     λ ¬∃n → ¬∃n ((succ k) ,, refl)   


  MP≡→isWFminCor→isWFseq- : MP≡ → R isWFminCor → R isWFseq-
  MP≡→isWFminCor→isWFseq- mp≡ wfmc s s-inc =
    isWFminCor→Cor¬¬ wfmc (λ a → ¬ Σ[ k ∈ ℕ ] (s k ≡ a) )
                    (cor→seqLemma mp≡ s s-inc) (s zero)
                    λ ¬Ex → ¬Ex ((0 ,, refl ))

  corDNE→isWFcor¬¬→isWFcor : (∀ P → corDNE R P) → R isWFcor¬¬ → R isWFcor
  corDNE→isWFcor¬¬→isWFcor corDNE-all RisWFcor¬¬ x φ φ∈Cor = corDNE-all φ φ∈Cor x (RisWFcor¬¬ φ φ∈Cor x)

module AccDNEWeakImplications {A : Set} (R : 𝓡 A) (acc∈DNE : AccDNE R) where
  -- 3. Implications relying on ¬¬-closure of accessibility
  isWFacc¬¬→¬¬isWFacc : R isWFacc¬¬ → ¬¬ (R isWFacc)
  isWFacc¬¬→¬¬isWFacc RisWFacc¬¬ ¬RisWFacc  = ¬RisWFacc λ x → acc∈DNE x (RisWFacc¬¬ x)

  ¬¬isWFacc→isWFacc : ¬¬ (R isWFacc) → R isWFacc
  ¬¬isWFacc→isWFacc ¬¬isWFaccR = λ x → acc∈DNE x (λ ¬accx → ¬¬isWFaccR (λ ∀acc → ¬accx (∀acc x ) ))

  ¬¬isWFind→isWFind : ¬¬ (R isWFind) → R isWFind
  ¬¬isWFind→isWFind ¬¬isWFindR = isWFacc→isWFind (¬¬isWFacc→isWFacc g) 
    where   g : ¬¬ (R isWFacc)
            g = λ ¬Racc → ¬¬isWFindR (λ Rind → ¬Racc (isWFind→isWFacc Rind ) )
