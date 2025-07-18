open import Relations.Relations
open import Relations.FinitelyBranching
open import Predicates
open import Logic
open import Datatypes using (ℕ; zero;  succ)
open import Relations.Seq
open import ARS.Properties
open import ARS.Implications

module ARS.SMImplications {A : Set} (R : 𝓡 A) where
  -- should be easy, following the same thing for SN/WF

  open LocalProperties {R = R}
  open MiscProperties R

  SM- : 𝓟 A
  SM- = ∁ (∁ SM)

  SMseq- : 𝓟 A
  SMseq- = ∁ (∁ SMseq )

  -- maybe? not?
  SM⊆SMseq : SM ⊆ SMseq
  SM⊆SMseq = ?

  -- definitely yes
  SM-⊆SMseq- : SM- ⊆ SMseq-
  SM-⊆SMseq- = ?

  -- maybe?
  FB∧dec→SMseq-⊆SM- : R isFBRel → dec (∁ SM) → SM- ⊆ SMseq-
  FB∧dec→SMseq-⊆SM- = ?
