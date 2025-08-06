-- {-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Classical
open import Relations.Decidable
open import Relations.ClosureOperators
open import Relations.Seq

module Relations.WellFounded.Wellfounded where

open import Relations.WellFounded.WFDefinitions public
open import Relations.WellFounded.WFWeakDefinitions public
open import Relations.WellFounded.WFBasicImplications public
open import Relations.WellFounded.WFWeakImplications public
open BasicImplications


open import Relations.FinitelyBranching
-- Implications relying on finite branching of the relation.
module FBImplications {A : Set} {R : 𝓡 A} (RisFB : (~R R) isFB) where

  -- May 2nd note: This must exist somewhere in general form?
  RisWF→¬¬RisWF : ∀ {a} → (R -accessible) a → ¬ (¬ (R -accessible) a)
  RisWF→¬¬RisWF RisWF ¬RisWF = ∅ (¬RisWF RisWF)

  -- REF: Move to WFWeakDefinitions?
  FB→isWFminDNE-→isWFacc- : isWFminDNE- R → isWFacc- R
  FB→isWFminDNE-→isWFacc- RisWF x₀ x₀∉acc =
    RisWF (∁ (R -accessible)) (λ a nnnac ac → ∅ (nnnac (RisWF→¬¬RisWF ac))) x₀∉acc f
      where f : ¬ Σ-syntax A (R - ∁ (R -accessible)-minimal)
            f (z ,, z∉acc , z∈min) =
              FB→DNS (~R R) (R -accessible) z (RisFB z)
                     (λ y Ryx y∉acc → z∈min y y∉acc Ryx )
                     λ za → z∉acc (acc za)
  

  -- When FB holds, ¬¬-accessibility is inductive
  -- REF: The below isn't used, shall we remove it?
  FB→ind∁∁acc : R -inductive (∁ ∁ R -accessible)
  FB→ind∁∁acc x H x∉acc = FB→DNS (~R R) (R -accessible) x (RisFB x) H (λ f → x∉acc (acc f) )

  -- For finitely branching relations, isDec implies MinDec
  open import Lists
  -- REF: Move this to FB?
  FB→isDec→isMinDec : R isDec → R isMinDec
  FB→isDec→isMinDec RisDec x₀ with decList∃ (~R R x₀) (λ _ → RisDec) (fst (RisFB x₀))
  ... | in2 ∄y = in2 (λ y Ryx₀ →
   ∄y (List∃intro (~R R x₀) (fst (RisFB x₀)) y (snd (RisFB x₀) y Ryx₀ , Ryx₀)))
  ... | in1 ∃y with List∃elim (~R R x₀) (fst (RisFB x₀)) ∃y
  ... | (y ,, _ , Ryx₀) = in1 (y ,, Ryx₀ )

open FBImplications public

module MinimalComplement {A : Set} (R : 𝓡 A) where
  open import Relations.Coreductive R

  -- A variation of ``minimal'' with focus on the complement of the given predicate
  isWFmin+ : Set₁
  isWFmin+ = ∀ (P : 𝓟 A) → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x) )

  -- isWFmin+, but restricted to coreductive predicates
  isWFminCor+ : Set₁
  isWFminCor+ = ∀ (P : 𝓟 A) → _-coreductive_ P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∉ P × (∀ x → R x m → P x))

  -- a weaker variation
  isWFminCor : Set₁
  isWFminCor = ∀ (P : 𝓟 A) → _-coreductive_ P → ∀ {a : A} → a ∉ P → Σ[ m ∈ A ] (m ∈ R - ∁ P -minimal)

  isWFminCor→Cor¬¬ : isWFminCor → ∀ P → _-coreductive_ P → ∀ x → ¬¬ P x
  isWFminCor→Cor¬¬ iwfc P Pco x ¬px with iwfc P Pco ¬px
  ... | (y ,, ¬py , ymin) with Pco y ¬py
  ... | (z ,, Rzy , ¬pz) = ymin z ¬pz Rzy

  -- Cor¬¬ is really a variation of isWFind- :
  -- ∀ P → P is coreductive → ∀ x → x ∈ ∁ (∁ P)
  -- Should we just call this isWFcor- or something?

  Cor¬¬→isWFminCor : (∀ P → _-coreductive_ P → ∀ x → ¬¬ P x) → isWFminCor
  Cor¬¬→isWFminCor H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFminCor+→isWFminCor : isWFminCor+ → isWFminCor
  isWFminCor+→isWFminCor RisWFminCor+ P Pcor a∉P with RisWFminCor+ P Pcor a∉P
  ... | (x ,, x∉P , H) = x ,, x∉P , λ y y∉P Ryx → y∉P (H y Ryx)

  Cor¬¬→isWFminCor+ : (∀ P → _-coreductive_ P → ∀ x → ¬¬ P x) → isWFminCor+
  Cor¬¬→isWFminCor+ H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFminCor→isWFminCor+ : isWFminCor → isWFminCor+
  isWFminCor→isWFminCor+ wfmc = Cor¬¬→isWFminCor+ (isWFminCor→Cor¬¬ wfmc )

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

  isWFminDNE→Cor¬¬ : R isWFminDNE → ∀ P → _-coreductive_ P → ∀ a → ¬¬ P a
  isWFminDNE→Cor¬¬ RisWFmin = isWFminCor→Cor¬¬
    (isWFminCor+→isWFminCor (isWFminDNE→isWFminCor+  RisWFmin))

  isWFminDNE-→Cor¬¬ : isWFminDNE- R → ∀ P → _-coreductive_ P → ∀ a → ¬¬ P a
  isWFminDNE-→Cor¬¬ WFR P Pcor a a∉P = WFR (∁ P) (λ x z z₁ → z (λ z₂ → z₂ z₁)) a∉P f
    where f : _
          f (m ,, m∉P , mmin) with Pcor m m∉P
          ... | (n ,, Rnm , n∉P) = mmin n (λ _ → mmin n n∉P Rnm) Rnm

  -- This implication also follows from isWFminDNE-→isWFmin-→isWFseq-→isWFaccc- (with accCor)
  accCor∧isWFminDNE-→isWFacc- : _-coreductive_ (R -accessible) → isWFminDNE- R → isWFacc- R
  accCor∧isWFminDNE-→isWFacc- accCor RisWF = isWFminDNE-→Cor¬¬ RisWF (R -accessible) accCor

  -- A Noteworthy Consequence
  accCorec→isWFseq-→isWFacc- : _-coreductive_ (R -accessible) → isWFseq- R → isWFacc- R
  accCorec→isWFseq-→isWFacc- AccisCor RisWFseq- a a∉acc = RisWFseq- seq seq-inc  where
    open CorSequence (CS {R -accessible} {AccisCor} (a ,, a∉acc))


  isWFseq-→isWFminCor+ : isWFseq- R → isWFminCor+
  isWFseq-→isWFminCor+ RisWFseq P CI {a} ¬pa =  ∅ (RisWFseq seq seq-inc) where
    open CorSequence (CS {P} {CI} (a ,, ¬pa))

  -- The converse is not provable,
  -- because the complement of the image of a sequence is not coreductive (at least not constructively).

  -- isWFminCor+→isWFseq- : isWFminCor+ → isWFseq- R
  -- isWFminCor+→isWFseq- WFmc s sinc
  --   with WFmc (λ x → Σ[ b ∈ ℕ ] (∀ k → k ≤ b → ¬ x ≡ s k) → Σ[ l ∈ ℕ ] → x ≡ s l) ... = {!   !}

  accCorec→isWFminCor+→isWFacc- : _-coreductive_ (R -accessible) → isWFminCor+ → isWFacc- R
  accCorec→isWFminCor+→isWFacc- acc∈Cor WFmc a a∉acc
    with WFmc (R -accessible) acc∈Cor a∉acc
  ... | (m ,, m∉acc , p) = m∉acc (acc p)

  open import Lists


  RisFBRel→accWDec→accCor : (~R R) isFBRel → dec (∁ (R -accessible)) → _-coreductive_ (R -accessible)
  RisFBRel→accWDec→accCor RisFBRel accWDec  =
      FBRel∧WDec→CorP RisFBRel (R -accessible) accWDec (λ x  → acc)


  -- RisFB→decNF→accCor : R isFB → dec (RMin R) → _-coreductive_ (R -accessible)
  -- RisFB→decNF→accCor RisFB decNF x x∉acc with FB→DNS R (R -accessible) x (RisFB x)
  -- ... | accDNS = {!   !}


  -- If the relation is finitely branching, then the complement of the image of each decreasing sequence is coreductive.
  cor→seqLemma : MP≡ → (s : ℕ → A) → s ∈ (R -decreasing) → _-coreductive_ (λ a → ¬ Σ-syntax ℕ (λ k → s k ≡ a))
  cor→seqLemma mp≡ s s-inc x ¬¬x∈s with mp≡ s x ¬¬x∈s
  ... | k ,, sk≡x = (s (succ k)) ,, transp (R (s (succ k))) sk≡x (s-inc (k)) ,
     λ ¬∃n → ¬∃n ((succ k) ,, refl)   

  isWFminCor+→isWFseq- : MP≡ → isWFminCor → isWFseq- R
  isWFminCor+→isWFseq- mp≡ wfmc s s-inc =
    isWFminCor→Cor¬¬ wfmc (λ a → ¬ Σ[ k ∈ ℕ ] (s k ≡ a) )
                    (cor→seqLemma mp≡ s s-inc) (s zero)
                    λ ¬Ex → ¬Ex ((0 ,, refl ))

module ClassicalImplications {A : Set} (R : 𝓡 A) where

  {- We will consider four decidability hypotheses here:
  1. isDec    : ∀xy. Rxy ⊔ ¬Rxy
  2. isMinDec : ∀x. (∃y. Ryx) ⊔ (∀y.¬Ryx)
  3. AccDNE   : ∀x. ¬x∉acc → x∈acc
  4. AccCor   : R -coreductive (R -accessible)
  -- (Recall that, for FB relations, 1 → 2)
  -}
-- REF: Move to WFBasicImplications
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
  -- REF: Move to WFBasicImplications
  DNEacc→isWFminDNE→isWFacc : AccDNE → R isWFminDNE → R isWFacc
  DNEacc→isWFminDNE→isWFacc dne wfDNE x = dne x f where
          f : ¬¬ (x ∈ R -accessible)
          f x∉acc with wfDNE (∁ (R -accessible)) (λ y nnny ya → nnny (λ z → z ya)) x x∉acc
          ... | (y ,, y∉acc , yIH) = y∉acc (acc λ z Rzy → dne z (λ z∉acc → yIH z z∉acc Rzy ) )

  -- Double negation shift for accessibility (global)
  -- REF: Move to WFWeakDefinitions all three below?
  isWFacc-→¬¬isWFacc : AccDNE → isWFacc- R → ¬¬ (R isWFacc)
  isWFacc-→¬¬isWFacc AccDNE RisWFacc- ¬RisWFacc  = ¬RisWFacc λ x → AccDNE x (RisWFacc- x)

  ¬¬isWFacc→isWFacc : AccDNE → ¬¬ (R isWFacc) → R isWFacc
  ¬¬isWFacc→isWFacc AccDNE ¬¬isWFaccR = λ x → AccDNE x (λ ¬accx → ¬¬isWFaccR (λ ∀acc → ¬accx (∀acc x ) ))

  ¬¬isWFind→isWFind : AccDNE → ¬¬ (R isWFind) → R isWFind
  ¬¬isWFind→isWFind AccDNE ¬¬isWFindR = isWFacc→isWFind (¬¬isWFacc→isWFacc (AccDNE) g )
    where g = λ ¬Racc → ¬¬isWFindR (λ Rind → ¬Racc (isWFind→isWFacc Rind ) )
