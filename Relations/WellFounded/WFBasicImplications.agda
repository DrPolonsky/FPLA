{-# OPTIONS --allow-unsolved-metas #-}
open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Classical
open import Relations.Decidable
open import Relations.ClosureOperators
open import Relations.Seq
-- TODO: Remove unused imports
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

module BasicImplications {A : Set} {R : 𝓡 A} where
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

  -- -- A correct(?) but non-terminating proof.
  -- {-# TERMINATING #-}
  -- isWFseq→isWFacc : R isWFseq → R isWFacc
  -- isWFseq→isWFacc R∈WFs x = acc (λ y Ryx → isWFseq→isWFacc R∈WFs y )

  WFseq+⊆WFseq : WFseq+ R ⊆ WFseq R
  WFseq+⊆WFseq x x∈seq+ s s0≡x with x∈seq+ s s0≡x
  ... | k ,, n  = k ,, n

  WFmin→WFcor : R isWFmin → R isWFcor 
  WFmin→WFcor RisWFmin = {!   !} 

  WFminDNE→WFcor : R isWFminDNE → R isWFcor 
  WFminDNE→WFcor RisWFminDNE x P P∈Cor with RisWFminDNE (∁ P) (¬¬Closed∁ P) x 
  ...| z = {!   !} 

  corP : 𝓟 A → 𝓟 A 
  corP P x = Σ[ y ∈ A ] ((R ⋆) y x)

  WFcor→WFminDNE : R isWFcor → R isWFminDNE 
  WFcor→WFminDNE RisWFcor P P∈DNE x x∈P = {!   !} 

  WFacc→WFcor : ∀ x → x ∈ WFacc R → WFcor R x
  WFacc→WFcor x (acc x∈acc) P P∈Cor = {!   !} 

  -- WFseq⊆WFseq+ : WFseq R ⊆ WFseq+ R
  -- WFseq⊆WFseq+ x x∈seq s s0≡x with x∈seq s s0≡x
  -- ... | k ,, n = k ,, {!   !}

  {- This formulation of WFseq+ is wrong:
  Consider ARS a -> b.
  Consider the sequence s(k) = a.
  Then s(k) is not a normal form, and the sequence s does not contain a normal form.
  Yet every sequence in this ARS does contain an element not reducing to its successor.

  Say that s : ℕ → A is *almost increasing* if for all n,
  either s(n) -> s(n+1) or s(n) is a normal form.

  WFseq+ could be something like: "every almost increasing sequence ends in a normal form".
  (IE, ∀ s : ℕ → A, AlmostIncreasing(s) → Σ[ n ∈ ℕ ] (s n ∈ NF ).)

  Let's check that such WFseq+ would indeed be equivalent to WFseq.
  1. WFseq⊆WFseq+. Assume WFseq.  Let s be given, suppose s is almost increasing.
  By assumption, exists k s.t. s(k) does not reduce to s(k+1).
  Since s is almost increasing, s(k) must be a normal form.
  2. WFseq+⊆WFseq.
  (That is, if every almost increasing sequence contains/ends in a normal form,
  then every sequence contains an element not reducing to its successor.)
  Classical argument.  Assume WFseq+.
  Let s be a sequence.
  By excluded middle, either s is almost increasing, or
  there exists an n, such that s(n) is neither a normal form, nor s(n) -> s(n+1).
  This n yields an index on which s does not reduce to its successor.
-}

open BasicImplications 

module DecdabilityImplications {A : Set} (R : 𝓡 A) where -- Using R isDec
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

module AccDNEImplications {A : Set} (R : 𝓡 A) (acc∈DNE : AccDNE R) where
  -- 3. Implications relying on ¬¬-closure of accessibility
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

  MP→isWFcor→isWFseq : R isWFcor → R isWFseq
  MP→isWFcor→isWFseq RisWFcor s with RisWFcor (s 0) (λ x → ((R ⋆) x (s 0) ) → ¬ (Σ[ k ∈ ℕ ] ((R ⋆) (s k) x))) {!   !} ε⋆  
  ... | z  = ∅ (z (0 ,, ε⋆))
