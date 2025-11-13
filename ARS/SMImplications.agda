open import Relations.Relations
open import Relations.FinitelyBranching
open import Predicates
open import Logic
open import Datatypes using (ℕ; zero;  succ)
open import Relations.Seq
open import ARS.Properties
open import ARS.Implications



module ARS.SMImplications {A : Set} (R : 𝓡 A) where
  open LocalProperties {R = R}
  open MiscProperties R

  SM- : 𝓟 A
  SM- = ∁ (∁ SM)

  SMseq- : 𝓟 A
  SMseq- = ∁ (∁ SMseq )

  isSM- : Set
  isSM- = ∀ x → x ∈ SM- 

  isSMseq- : Set 
  isSMseq- = ∀ x → x ∈ SMseq- 

  inc∧SMseq→MF : ∀ (f : ℕ → A) → f ∈ R -increasing → f 0 ∈ SM → Σ[ i ∈ ℕ ] ((f i) ∈ MF)
  inc∧SMseq→MF f f-inc (MF⊆SM .(f 0) f0∈MF) = zero ,, f0∈MF
  inc∧SMseq→MF f f-inc (SMind .(f 0) f0acc) with inc∧SMseq→MF (f ∘ succ) (λ n → f-inc (succ n)) (f0acc (f (succ 0)) (f-inc 0)) 
  ... | i ,, fi∈MF = succ i ,, fi∈MF  
  
  SM⊆SMseq : SM ⊆ SMseq
  SM⊆SMseq .(f zero) (MF⊆SM .(f zero) x∈MF) f refl f-inc = zero ,, x∈MF
  SM⊆SMseq .(f zero) f0∈SM@(LocalProperties.SMind .(f zero) x∈acc) f refl f-inc = inc∧SMseq→MF f f-inc f0∈SM

  SM-⊆SMseq- : SM- ⊆ SMseq-
  SM-⊆SMseq- x ¬¬x∈SM ¬x∈SMseq = ¬¬x∈SM (λ smx → ¬x∈SMseq (SM⊆SMseq x smx))

  open import Relations.WellFounded.WFDefinitions using (_-coreductive_) 
  open import Relations.Coreductive (~R R)

  FBrel→decCSM→SMcor : R isFBRel → dec (∁ (SM)) → (~R R) -coreductive (SM)
  FBrel→decCSM→SMcor RisFBRel SMwDec = 
    indP→CorP RisFBRel SM SMwDec SMind 

  SMCor→SMseq-→SM- : (~R R) -coreductive (SM) → isSMseq- → isSM-    
  SMCor→SMseq-→SM- SMisCor RisSMseq- a a∉SM- = RisSMseq- a λ H → seq⊆CP ((fst (H seq refl seq-inc))) (MF⊆SM (seq (fst (H seq refl seq-inc))) ((snd (H seq refl seq-inc) )))  where 
    open CorSequence (CS {SM} {SMisCor} (a ,, a∉SM-))      

  
  FB∧dec→SMseq-⊆SM- : R isFBRel → dec (∁ SM) → isSMseq- → isSM-
  FB∧dec→SMseq-⊆SM- RisFBRel SMwDec RisSMseq- with FBrel→decCSM→SMcor RisFBRel SMwDec 
  ... | SMisCor = SMCor→SMseq-→SM- SMisCor RisSMseq-