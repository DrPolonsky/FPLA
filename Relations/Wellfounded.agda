{-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Classical
open import Relations.Decidable
open import Relations.ClosureOperators
open import Relations.Seq

module Relations.Wellfounded where

open import Relations.WFDefinitions public
open import Relations.WeakWFDefinitions public

module BasicImplications {A : Set} {R : 𝓡 A} where

  -- Accessibility is the least inductive predicate
  acc⊆ind : ∀ (φ : 𝓟 A) → R -inductive φ → R -accessible ⊆ φ
  acc⊆ind φ φisRind x (acc IH) = φisRind x (λ y Ryx → acc⊆ind φ φisRind y (IH y Ryx) )

  -- acc⊆WFseq : R -accessible ⊆ WFseq R
  -- acc⊆WFseq a (acc ac) s s0=a = acc⊆WFseq (s 1) {!   !} {!   !} {!   !}
  --
  ¬acc : ∀ {x : A} → x ∉ R -accessible → ¬ (∀ y → R y x → y ∈ R -accessible)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

  ¬ind : ∀ (P : 𝓟 A) → R -inductive P → ∀ x → ¬ (P x) → ¬ (∀ y → R y x → P y)
  ¬ind P Pind x ¬Px ∀y = ¬Px (Pind x ∀y )

  wf→irrefl : R isWF → ∀ x → ¬ R x x
  wf→irrefl RisWF x = go x (RisWF x) where
    go : ∀ y → y ∈ R -accessible → ¬ R y y
    go y (acc Hy) Ryy = go y (Hy y Ryy) Ryy

  -- implications between the base definitions
  isWFacc→isWFind : R isWFacc → R isWFind
  isWFacc→isWFind wfAcc x φ φ-ind = acc⊆ind φ φ-ind x (wfAcc x)

  isWFind→isWFacc : R isWFind → R isWFacc
  isWFind→isWFacc wfInd x = wfInd x (WFacc R ) λ y → acc

  isWFmin→isWFminDNE : R isWFmin → R isWFminDNE
  isWFmin→isWFminDNE RisWFmin P PDNE = RisWFmin P

  isWFminDNE→isWFminEM : R isWFminDNE → R isWFminEM
  isWFminDNE→isWFminEM RisWFminDNE P PEM = RisWFminDNE P (dec→¬¬Closed P PEM )

  isWFmin→isWFseq : R isWFmin → R isWFseq
  isWFmin→isWFseq wfMin s with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) (s zero) (zero ,, refl)
  ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )

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


open WeakImplications public

-- Implications relying on decidability of minimality.
module WFMinDecImplications {A : Set} (R : 𝓡 A) (dM : R isMinDec) where

  dMseq : A → ℕ → A
  dMseq a0 zero = a0
  dMseq a0 (succ n) with dM (dMseq a0 n)
  ... | in1 (b ,, bRsn) = b
  ... | in2 x = dMseq a0 n

  ¬¬∃seqDec : ∀ a → ¬¬ (   (Σ[ k ∈ ℕ ] ∀ x → ¬ R x (dMseq a k))
                         ⊔ (∀ k → R (dMseq a (succ k)) (dMseq a k)))
  ¬¬∃seqDec a ¬EM = ¬EM (in2 f) where
    f : (dMseq a) ∈ R -decreasing
    f k with dM (dMseq a k) | dMseq a (succ k) in e
    ... | in1 (c ,, Rcsk) | b = transp (~R R (dMseq a k)) e Rcsk
    ... | in2 x∈NF | b = ∅ (¬EM (in1 (k ,, x∈NF)))


open WFMinDecImplications public
open import Relations.FinitelyBranching
-- Implications relying on finite branching of the relation.
module FBImplications {A : Set} {R : 𝓡 A} (RisFB : R isFB) where

  -- May 2nd note: This must exist somewhere in general form? 
  RisWF→¬¬RisWF : ∀ {a} → (R -accessible) a → ¬ (¬ (R -accessible) a)
  RisWF→¬¬RisWF RisWF ¬RisWF = ∅ (¬RisWF RisWF) 
  
  FB→isWFminDNE-→isWFacc- : isWFminDNE- R → isWFacc- R
  FB→isWFminDNE-→isWFacc- RisWF x₀ x₀∉acc =
    RisWF (∁ (R -accessible)) (λ a nnnac ac → ∅ (nnnac (RisWF→¬¬RisWF ac))) x₀∉acc f
      where f : ¬ Σ-syntax A (R - ∁ (R -accessible)-minimal)
            f (z ,, z∉acc , z∈min) =
              FB→DNS R (R -accessible) z (RisFB z)
                     (λ y Ryx y∉acc → z∈min y y∉acc Ryx )
                     λ za → z∉acc (acc za)
  
  -- When FB holds, ¬¬-accessibility is inductive
  FB→ind∁∁acc : R -inductive (∁ ∁ R -accessible)
  FB→ind∁∁acc x H x∉acc = FB→DNS R (R -accessible) x (RisFB x) H (λ f → x∉acc (acc f) )

  -- For finitely branching relations, isDec implies MinDec
  open import Lists
  FB→isDec→isMinDec : R isDec → R isMinDec
  FB→isDec→isMinDec RisDec x₀ with decList∃ (~R R x₀) (λ _ → RisDec) (fst (RisFB x₀))
  ... | in2 ∄y = in2 (λ y Ryx₀ →
   ∄y (List∃intro (~R R x₀) (fst (RisFB x₀)) y (snd (RisFB x₀) y Ryx₀ , Ryx₀)))
  ... | in1 ∃y with List∃elim (~R R x₀) (fst (RisFB x₀)) ∃y
  ... | (y ,, _ , Ryx₀) = in1 (y ,, Ryx₀ )

  -- May 2nd: Does this want moving to misc?
  FB→isWFminDNE→isWFseq : R isWFminDNE → R isWFseq
  FB→isWFminDNE→isWFseq wfMinDNE s = {!    !} where
    RisWFseq- : isWFseq- R
    RisWFseq- = isWFmin-→isWFseq- R (isWFminDNE-→isWFmin- R (isWFminDNE→isWFminDNE- R wfMinDNE))
    P : 𝓟 A
    P x = Σ[ n ∈ ℕ ] (x ≡ s n × ¬ (s ∘ add n) ∈ R -decreasing)
    ps0 : P (s 0)
    ps0 = 0 ,, (refl , RisWFseq- _ )
    CCP⊆P : ¬¬Closed P
    CCP⊆P x ¬x∉P = {!    !}

  -- with wfMin (λ a → Σ[ n ∈ ℕ ] (s n ≡ a)) (s zero) (zero ,, refl)
  -- ... | x ,, (k ,, p) , H = (k ,, λ Ryx → H (s (succ k)) (succ k ,, refl ) (transp (R (s (succ k))) p Ryx ) )



open FBImplications public

module MinimalComplement {A : Set} (R : 𝓡 A) where
  _-coreductive_ : 𝓟 A → Set
  _-coreductive_ P = ∀ x → x ∉ P → Σ[ y ∈ A ] (R y x × y ∉ P)

  Cor→ind¬¬ : ∀ (P : 𝓟 A) → _-coreductive_ P → R -inductive (∁ (∁ P))
  Cor→ind¬¬ P Pco x xind ¬Px with Pco x ¬Px
  ... | (y ,, Ryx , ¬Py) = xind y Ryx ¬Py

  -- A variation of ``minimal'' with focus on the complement of the given predicate
  isWFmin+ : Set₁
  isWFmin+ = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x) )

  -- isWFmin+, but restricted to coreductive predicates
  isWFminCor+ : Set₁
  isWFminCor+ = ∀ (P : 𝓟 A) → _-coreductive_ P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x))

  -- a weaker variation
  isWFminCor : Set₁
  isWFminCor = ∀ (P : 𝓟 A) → _-coreductive_ P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∈ R - ∁ P -minimal)

  -- Implications involving complements/coreductive
  isWFmin+→isWFind- : isWFmin+ → isWFind- R
  isWFmin+→isWFind- RisWF P Pind x ¬px with RisWF P ¬px
  ... | (y ,, ¬py , yind) = ¬py ((Pind y yind))

  isWFmin+→isWFmin- : isWFmin+ → isWFmin- R
  isWFmin+→isWFmin- Rmin+ P {d} p ¬∃minP with Rmin+ (∁ P ) (λ x → x p)
  ... | (a ,, ¬¬Pa , aMin) = ¬¬Pa (λ pa → ¬∃minP ((a ,, pa , λ y Py Rya → aMin y Rya Py )) )

  isWFmin+→isWFminDNE : isWFmin+ → R isWFminDNE
  isWFmin+→isWFminDNE RisWFmin+ P ∁∁P⊆P a a∈P with RisWFmin+ (∁ P) (λ a∉P → a∉P a∈P)
  ... | x ,, ¬¬x∈P , xmin = x ,, ∁∁P⊆P x ¬¬x∈P , (λ y y∈P Ryx → xmin y Ryx y∈P)

  isWFminDNE→isWFminCor+ : R isWFminDNE → isWFminCor+
  isWFminDNE→isWFminCor+ RisWFminDNE P Pco {a} a∉P
    with  RisWFminDNE (∁ P) DNS¬ a a∉P
    where DNS¬ = λ x ¬Px ¬¬Px → ¬Px (λ z → z ¬¬Px)
  ... | (y ,, ¬Py , ymin) with Pco y ¬Py
  ... | (z ,, Rzy , ¬Pz) = ∅ (ymin z ¬Pz Rzy)

  isWFminCor+→isWFminCor : isWFminCor+ → isWFminCor
  isWFminCor+→isWFminCor RisWFminCor+ P Pcor a∉P with RisWFminCor+ P Pcor a∉P
  ... | (x ,, x∉P , H) = x ,, x∉P , λ y y∉P Ryx → y∉P (H y Ryx)

  isWFminCor→Cor¬¬ : isWFminCor → ∀ P → _-coreductive_ P → ∀ x → ¬¬ P x
  isWFminCor→Cor¬¬ iwfc P Pco x ¬px with iwfc P Pco ¬px
  ... | (y ,, ¬py , ymin) with Pco y ¬py
  ... | (z ,, Rzy , ¬pz) = ymin z ¬pz Rzy

  isWFminDNE→Cor¬¬ : R isWFminDNE → ∀ P → _-coreductive_ P → ∀ a → ¬¬ P a
  isWFminDNE→Cor¬¬ RisWFmin = isWFminCor→Cor¬¬
    (isWFminCor+→isWFminCor (isWFminDNE→isWFminCor+  RisWFmin))

  CorSequence : ∀ P → _-coreductive_ P → Σ[ a ∈ A ] (a ∉ P) → ℕ → Σ[ e ∈ A ] (e ∉ P)
  CorSequence P CI aH zero = aH
  CorSequence P CI (a ,, Ha) (succ n) with CorSequence P CI (a ,, Ha) n
  ... | (a' ,, Ha') with CI a' Ha'
  ... | (x ,, Rxa , x∉P) = (x ,, x∉P)

  CorSequence-inc : ∀ P → (PCor : _-coreductive_ P) (init : Σ[ a ∈ A ] (a ∉ P)) →
                           (R -decreasing) (fst ∘ CorSequence P PCor init)
  CorSequence-inc P PCor init k with CorSequence P PCor init k
  ... | (a ,, Ha) with PCor a Ha
  ... | (x ,, Rxa , x∉P) = Rxa

  -- A Noteworthy Consequence
  accCorec→isWFseq-→isWFacc- : _-coreductive_ (R -accessible) → isWFseq- R → isWFacc- R
  accCorec→isWFseq-→isWFacc- AccisCor RisWFseq- a a∉acc = RisWFseq- s s-inc where
    s     = fst ∘ CorSequence     (R -accessible) AccisCor (a ,, a∉acc)
    s-inc = CorSequence-inc (R -accessible) AccisCor (a ,, a∉acc)

  isWFseq-→isWFminCor+ : isWFseq- R → isWFminCor+
  isWFseq-→isWFminCor+ RisWFseq P CI {a} ¬pa
    with (CorSequence P CI (a ,, ¬pa)) | RisWFseq (fst ∘ CorSequence P CI (a ,, ¬pa)) (CorSequence-inc P CI (a ,, ¬pa))
  ... | c | H = ∅ H

module ClassicalImplications {A : Set} (R : 𝓡 A) where

  {- We will consider four decidability hypotheses here:
  1. isDec    : ∀xy. Rxy ⊔ ¬Rxy
  2. isMinDec : ∀x. (∃y. Ryx) ⊔ (∀y.¬Ryx)
  3. AccDNE   : ∀x. ¬x∉acc → x∈acc
  4. AccCor   : R -coreductive (R -accessible)
  -- (Recall that, for FB relations, 1 → 2)
  -}

  -- 1. For decidable relations, sequential well-foundedness is implied by the standard one
  isDec→isWFacc→isWFseq : R isDec → R isWFacc → R isWFseq
  isDec→isWFacc→isWFseq dR wfAcc s = f s (s zero) (wfAcc (s zero)) refl where
    f : ∀ (s : ℕ → A) (x : A) (x-acc : x ∈ R -accessible) (x=s0 : x ≡ s zero)
              → Σ[ k ∈ ℕ ] (¬ R (s (succ k)) (s k))
    f s x (acc xa) x=s0 with dR {s 1} {x}
    ... | in2 ¬Ryx = 0 ,, λ Rs1s0 → ¬Ryx (transp (R (s 1)) (~ x=s0) Rs1s0)
    ... | in1  Ryx with f (s ∘ succ) (s 1) (xa (s 1) Ryx) refl
    ... | i ,, p = succ i ,, p

  isDec→isWFind→isWFseq : R isDec → R isWFind → R isWFseq
  isDec→isWFind→isWFseq dR wfInd = isDec→isWFacc→isWFseq dR (isWFind→isWFacc wfInd)

  -- 2. Implications relying on decidability of minimality.
  module WFseqImplications {A : Set} (R : 𝓡 A) (dM : R isMinDec) where
  {-  Very hard to imply isWFseq, almost nothing is provable.
      isWFminDNE→isWFseq requires: ¬¬Closed (Σa:ℕ. s n ≡ a)
      isWFmin+→isWFseq requires: same as above
      isWFminEM→isWFseq requires: decidability of the above predicate
      isWFminCor→isWFseq cannot find the index in the sequence
      isWFmin→isWFseq is provable with no additional assumptions
    -}

  module WFDNE {A : Set} (R : 𝓡 A) where
  -- 3. Implications relying on ¬¬-closure of accessibility
  AccDNE : Set
  AccDNE = ¬¬Closed (R -accessible)

  -- April 28th: Todo fix this
  DNEacc→isWFminDNE→isWFacc : AccDNE → R isWFminDNE → R isWFacc
  DNEacc→isWFminDNE→isWFacc dne wfDNE x = dne x f where
          f : ¬¬ (x ∈ R -accessible)
          f x∉acc with wfDNE (∁ (R -accessible)) (λ y nnny ya → nnny (λ z → z ya)) x x∉acc
          ... | (y ,, y∉acc , yIH) = y∉acc (acc λ z Rzy → dne z (λ z∉acc → yIH z z∉acc Rzy ) )
    
  -- Double negation shift for accessibility (global)
  isWFacc-→¬¬isWFacc : AccDNE → isWFacc- R → ¬¬ (R isWFacc)
  isWFacc-→¬¬isWFacc AccDNE RisWFacc- ¬RisWFacc  = ¬RisWFacc λ x → AccDNE x (RisWFacc- x)

  ¬¬isWFacc→isWFacc : AccDNE → ¬¬ (R isWFacc) → R isWFacc
  ¬¬isWFacc→isWFacc AccDNE ¬¬isWFaccR = λ x → AccDNE x (λ ¬accx → ¬¬isWFaccR (λ ∀acc → ¬accx (∀acc x ) ))

  ¬¬isWFind→isWFind : AccDNE → ¬¬ (R isWFind) → R isWFind
  ¬¬isWFind→isWFind AccDNE ¬¬isWFindR = isWFacc→isWFind (¬¬isWFacc→isWFacc (AccDNE) g )
    where g = λ ¬Racc → ¬¬isWFindR (λ Rind → ¬Racc (isWFind→isWFacc Rind ) )
