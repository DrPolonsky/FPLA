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

  isSM- : Set
  isSM- = ∀ x → x ∈ SM- 

  isSMseq- : Set 
  isSMseq- = ∀ x → x ∈ SMseq- 

  inc∧SMseq→MF : ∀ (f : ℕ → A) → f ∈ R -increasing → f 0 ∈ SM → Σ[ i ∈ ℕ ] ((f i) ∈ MF)
  inc∧SMseq→MF f f-inc (SMrec .(f 0) f0∈MF) = zero ,, f0∈MF
  inc∧SMseq→MF f f-inc (SMacc .(f 0) f0acc) with inc∧SMseq→MF (f ∘ succ) (λ n → f-inc (succ n)) (f0acc (f (succ 0)) (f-inc 0)) 
  ... | i ,, fi∈MF = succ i ,, fi∈MF  
  
  SM⊆SMseq : SM ⊆ SMseq
  SM⊆SMseq .(f zero) (SMrec .(f zero) x∈MF) f refl f-inc = zero ,, x∈MF
  SM⊆SMseq .(f zero) f0∈SM@(LocalProperties.SMacc .(f zero) x∈acc) f refl f-inc = inc∧SMseq→MF f f-inc f0∈SM

  SM-⊆SMseq- : SM- ⊆ SMseq-
  SM-⊆SMseq- x ¬¬x∈SM ¬x∈SMseq = ¬¬x∈SM (λ smx → ¬x∈SMseq (SM⊆SMseq x smx))

  -- maybe?
  -- Start with a lemma which mirrors RisFBRel→accWDec→accCor to imply sm is correductive. And then follow accCorec→isWFseq-→isWFacc- to complete the proof. ** July 23rd 

  open import Relations.Coreductive (R)
  open MinimalComplement R

  FBrel→decCSM→SMcor : R isFBRel → dec (∁ (SM)) → _-coreductive_ (SM)
  FBrel→decCSM→SMcor RisFBRel SMwDec = 
    FBRel∧WDec→CorP RisFBRel SM (λ z → SMacc _ (λ y → z)) SMwDec  

  -- Define CorSequence in Coreductive file and refactor here and wellfounded. All below needs uncommenting. 
  SMCor→SMseq-→SM- : _-coreductive_ (SM) → isSMseq- → isSM-    
  SMCor→SMseq-→SM- SMisCor RisSMseq- a a∉SM- = let 
      s : (x : ℕ) → A 
      s = fst ∘ CorSequence   (SM) SMisCor (a ,, a∉SM-) 
      s-inc = CorSequence-inc (SM) SMisCor (a ,, a∉SM-) 
    in RisSMseq- {!   !} {!   !}

  
  -- FB∧dec→SMseq-⊆SM- : R isFBRel → dec (∁ SM) → SMseq- ⊆ SM-
  -- FB∧dec→SMseq-⊆SM- RisFBRel SMwDec a RisSMseq- a∉SM- with FBrel→decCSM→SMcor RisFBRel SMwDec 
  -- ... | SMisCor = RisSMseq- {!   !} where 
  --   s = {!   !} 
  --   s-inc = {!   !} 



-- If we have a relation that is bp and rp, why is it difficult to show that it has the relation SM. Classically we can take the chain RPandBP -> SMseq -> SMseq- -> SM- -> SM We could show the BP∧RP∧(Classical assumptions) → SM 
-- WN SM -> SN. WN BP RP -> SN (constructively)?