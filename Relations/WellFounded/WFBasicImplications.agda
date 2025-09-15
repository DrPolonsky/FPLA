{-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Datatypes
open import Relations.Decidable
open import Relations.ClosureOperators

module Relations.WellFounded.WFBasicImplications where

open import Relations.WellFounded.WFDefinitions public
open import Relations.WellFounded.WFWeakDefinitions public
open import Relations.WellFounded.ClassicalProperties public

module PropertyImplications {A : Set} {R : 𝓡 A} where 
  -- Accessibility is the least inductive predicate
  acc⊆ind : ∀ (φ : 𝓟 A) → R -inductive φ → R -accessible ⊆ φ
  acc⊆ind φ φisRind x (acc IH) = φisRind x (λ y Ryx → acc⊆ind φ φisRind y (IH y Ryx) )

  ¬acc : ∀ {x : A} → x ∉ R -accessible → ¬ (∀ y → R y x → y ∈ R -accessible)
  ¬acc ¬xisRacc ∀yisRacc = ¬xisRacc (acc ∀yisRacc)

  -- May 2nd note: This must exist somewhere in general form?
  RisWF→¬¬RisWF : ∀ {a} → (R -accessible) a → ¬ (¬ (R -accessible) a)
  RisWF→¬¬RisWF RisWF ¬RisWF = ∅ (¬RisWF RisWF)

  ¬ind : ∀ (P : 𝓟 A) → R -inductive P → ∀ x → ¬ (P x) → ¬ (∀ y → R y x → P y)
  ¬ind P Pind x ¬Px ∀y = ¬Px (Pind x ∀y )

open PropertyImplications public

module ConstructiveImplications {A : Set} {R : 𝓡 A} where
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

-- SA: Can we remove corP? Sep 15
  corP : 𝓟 A → 𝓟 A 
  corP P x = Σ[ y ∈ A ] ((R ⋆) y x)

open ConstructiveImplications 

module DecdabilityImplications {A : Set} (R : 𝓡 A) (dR : R isDec) where
  isDec→isWFacc→isWFseq : R isWFacc → R isWFseq
  isDec→isWFacc→isWFseq wfAcc s = f s (s zero) (wfAcc (s zero)) refl where
    f : ∀ (s : ℕ → A) (x : A) (x-acc : x ∈ R -accessible) (x=s0 : x ≡ s zero)
              → Σ[ k ∈ ℕ ] (¬ R (s (succ k)) (s k))
    f s x (acc xa) x=s0 with dR {s 1} {x}
    ... | in2 ¬Ryx = 0 ,, λ Rs1s0 → ¬Ryx (transp (R (s 1)) (~ x=s0) Rs1s0)
    ... | in1  Ryx with f (s ∘ succ) (s 1) (xa (s 1) Ryx) refl
    ... | i ,, p = succ i ,, p

  isDec→isWFind→isWFseq : R isWFind → R isWFseq
  isDec→isWFind→isWFseq wfInd = isDec→isWFacc→isWFseq (isWFind→isWFacc wfInd)

module AccDNEImplications {A : Set} (R : 𝓡 A) (acc∈DNE : AccDNE R) where
  DNEacc→isWFminDNE→isWFacc : R isWFminDNE → R isWFacc
  DNEacc→isWFminDNE→isWFacc wfDNE x = acc∈DNE x f where
          f : ¬¬ (x ∈ R -accessible)
          f x∉acc with wfDNE (∁ (R -accessible)) (λ y nnny ya → nnny (λ z → z ya)) x x∉acc
          ... | (y ,, y∉acc , yIH) = y∉acc (acc λ z Rzy → acc∈DNE z (λ z∉acc → yIH z z∉acc Rzy ) )

module accCorImplications {A : Set} (R : 𝓡 A) (acc∈Cor : AccCor R) where 
  accCor∧isWFcor→isWFacc : R isWFcor → R isWFacc 
  accCor∧isWFcor→isWFacc RisWFcor x = RisWFcor x (R -accessible) acc∈Cor 

module MP≡Implications {A : Set} (R : 𝓡 A) (mp≡ : MP≡) where 
  MP→isWFminDNE→isWFseq : R isWFminDNE → R isWFseq
  MP→isWFminDNE→isWFseq RisWFminDNE s 
    with RisWFminDNE (λ x → Σ[ k ∈ ℕ ] (s k ≡ x)) (λ x → mp≡ s x ) (s 0) (0 ,, refl)     
  ... | y ,, (k ,, sk≡y) , ¬sz→Rzy  = k ,, 
    λ Rsk+1Rsk → ¬sz→Rzy (s (succ k)) ((succ k) ,, refl) 
      (transp (R (s (succ k))) sk≡y Rsk+1Rsk) 

-- SA: Sep 15th Do we want to keep this or scrap at this point?
  -- MP→isWFcor→isWFseq : R isWFcor → R isWFseq
  -- MP→isWFcor→isWFseq RisWFcor s with RisWFcor (s 0) (λ x → ((R ⋆) x (s 0) ) → ¬ (Σ[ k ∈ ℕ ] ((R ⋆) (s k) x))) f ε⋆  
  --   where 
  --     f : _ 
  --     f x H = ?
  -- ... | z  = ∅ (z (0 ,, ε⋆))
  -- try and build on this implication. Will probably need to apply MP≡ twice. 
  -- What correductive property associated with the sequence which if assumed to always be true would give a counterexample to the sequence?
  -- predicate cand: if you're in the image of s then none of your successors should be in the image of s
  -- Pred: Given x, the xomplement of sigma k 
{- 
  MP→isWFcor→isWFseq : R isWFcor → R isWFseq
  MP→isWFcor→isWFseq RisWFcor s = {!   !} -- ∅ (g (fst lr) snd lr) 
    where 
      g : ∀ (k : ℕ) → (¬(R ⋆) (s k) (s 0))
      g = {!   !} 
      f : R -coreductive (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) 
      f x x∉P with mp≡ s x (λ x∉s → x∉P (λ x∈s → ∅ (x∉s x∈s)))
      ... | k ,, sk≡x rewrite ~ sk≡x = (s (succ k)) ,, ( ?  , λ H → x∉P λ x₁ → fst (H (succ k ,, refl)) ,, λ R*ssucksk → snd (H (succ k ,, refl)) ? )           

      lr = RisWFcor (s 0) (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) f (0 ,, refl)
-}

module DNEcorImplications {A : Set} (R : 𝓡 A) (cor∈DNE : (P : 𝓟 A) → corDNE R P) where 
  WFmin→WFcor¬¬ : R isWFmin → ∀ (x : A) → (P : 𝓟 A) → R -coreductive P → ¬¬ (P x)
  WFmin→WFcor¬¬ RisWFmin x P Pcor x∉P with RisWFmin (∁ P) x x∉P   
  ... | m ,, m∉P , m∈min with Pcor m m∉P 
  ... | (z ,, (Rzm , z∉P)) = m∈min z z∉P Rzm 
    
  corDNE→WFmin→WFcor : R isWFmin → R isWFcor
  corDNE→WFmin→WFcor RisWFmin x P P∈cor with WFmin→WFcor¬¬ RisWFmin x P P∈cor 
  ...| nnPx = cor∈DNE P P∈cor x nnPx 

  acc→WFcorLocal :
    ∀ x → x ∈ R -accessible → WFcor R x
  acc→WFcorLocal x (acc IH) P Pcor =
    cor∈DNE P Pcor x (rec (acc IH))
    where
      rec : ∀ {z} → z ∈ R -accessible → ¬ (P z) → ⊥
      rec {z} (acc IHz) nz with Pcor z nz
      ... | (y ,, (Ryz , nPy)) = rec (IHz y Ryz) nPy

  corDNE→WFacc→WFcor : R isWFacc → R isWFcor
  corDNE→WFacc→WFcor RisWFacc x = acc→WFcorLocal x (RisWFacc x)

  corDNE→WFminDNE→WFcor : R isWFminDNE → R isWFcor
  corDNE→WFminDNE→WFcor RisWFminDNE x P Pcor = cor∈DNE P Pcor x ¬¬Px
    where 
      ¬¬Px : ¬¬ P x
      ¬¬Px ¬Px with RisWFminDNE (∁ P) (¬¬Closed∁ P) x ¬Px 
      ... | y ,, ¬Py , Ry⊆∁∁P with Pcor y ¬Py 
      ... | z ,, Rzy , ¬Pz = Ry⊆∁∁P z ¬Pz Rzy 

  open import Relations.Coreductive R
  open CorSequence

  corDNE→WFseq→WFcor : R isWFseq → R isWFcor 
  corDNE→WFseq→WFcor RisWFseq x P Pcor = cor∈DNE P Pcor x ¬¬Px 
    where 
      ¬¬Px : ¬¬ P x
      ¬¬Px ¬Px with (CS {Pcor = Pcor} (x ,, ¬Px)) 
      ...| cs with RisWFseq (seq cs)
      ...| k ,, ¬Rsk+1sk = ¬Rsk+1sk (seq-inc {Pcor = Pcor} cs k)  
      
-- SA: Sep 15th do we want to keep either of the remaining two proofs below?       
module WFseqImplications {A : Set} (R : 𝓡 A) where
-- Classical “negated universal → existential counterexample” on predecessors of z
  postulate
    ExistsBadPred :
      ∀ z → z ∈ ∁ (WFacc R) →
      Σ[ y ∈ A ] (R y z × y ∈ ∁ (WFacc R))

  -- Dependent choice along predecessors inside X = ∁ WFacc
  postulate
    DC-pre :
      (x : A) → x ∈ ∁ (WFacc R) →
      Σ[ f ∈ (ℕ → A) ]
        ( (f 0 ≡ x)
        × ((∀ (n : ℕ) → R (f (succ n)) (f n))
        × (∀ (n : ℕ) → f n ∈ ∁ (WFacc R))) )

  -- From WFseq, build a contradiction with any infinite descending chain
  WFseq→¬¬WFacc : R isWFseq → ∀ x → ¬¬ (x ∈ WFacc R)
  WFseq→¬¬WFacc WFs x notAcc
    with DC-pre x notAcc
  ... | (f ,, (refl , (dec , _)))
    with WFs f
  ... | (k ,, notStep) = ∅ (notStep (dec k))

  -- Close the double negation using AccDNE
  WFseq→WFacc :
    AccDNE R → R isWFseq → R isWFacc
  WFseq→WFacc acc∈DNE WFs x =
    acc∈DNE x (WFseq→¬¬WFacc WFs x)

module MP→isWFcor→isWFseq {A : Set} {R : 𝓡 A} (RisWFcor : R isWFcor) (s : ℕ → A) (mp≡ : MP≡) where 
  g : ∀ (k : ℕ) → (¬(R ⋆) (s k) (s 0))
  g = {!   !} 
  
  f : R -coreductive (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) 
  f x x∉P with mp≡ s x (λ x∉s → x∉P (λ x∈s → ∅ (x∉s x∈s)))
  ... | k ,, sk≡x rewrite ~ sk≡x 
    = (s (succ k)) ,,
      ( {!   !}  , λ H → x∉P λ x₁ → fst (H (succ k ,, refl)) ,,  
      λ R*ssucksk → snd (H (succ k ,, refl)) {!   !} )   

  ims∈cor : R -coreductive (λ x → ¬ Σ[ k ∈ ℕ ] ((s k) ≡ x))
  ims∈cor x x∉s with mp≡ s x x∉s 
  ... | k ,, sk≡x = s (succ k) ,, {!   !}           

  lr = RisWFcor (s 0) (λ x → Σ[ k ∈ ℕ ] ((s k) ≡ x) → (Σ[ k ∈ ℕ ] ( ¬ (R ⋆) (s k) x))) f (0 ,, refl)