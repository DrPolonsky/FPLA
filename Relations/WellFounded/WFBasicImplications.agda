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

  WFseq+⊆WFseq : WFseq+ R ⊆ WFseq R
  WFseq+⊆WFseq x x∈seq+ s s0≡x with x∈seq+ s s0≡x
  ... | k ,, n  = k ,, n

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
