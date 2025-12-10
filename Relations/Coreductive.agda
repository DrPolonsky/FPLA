open import Predicates
open import Logic
open import Relations.FinitelyBranching
open import Lists
open import Datatypes
open import Relations.Seq
open import Relations.Core
open import Relations.WellFounded.WFDefinitions
open import Classical
open import Relations.WellFounded.ClassicalProperties
open import Relations.Decidable

module Relations.Coreductive {A : Set} (R : 𝓡 A) where
  Cor→ind¬¬ : ∀ (P : 𝓟 A) → R -coreductive P → R -inductive (∁ (∁ P))
  Cor→ind¬¬ P Pco x xind ¬Px with Pco x ¬Px
  ... | (y ,, Ryx , ¬Py) = xind y Ryx ¬Py

  indP→CorP : (~R R) isFBRel → ∀ (P : 𝓟 A) → wdec (P) → R -inductive P → R -coreductive P
  indP→CorP RisFBRel P PwDec Rind a a∉P with FBRel∧WDec→EMRyx (~R R) RisFBRel P PwDec {a} 
  ... | in1 yes = yes
  ... | in2 no = ∅ (FB→DNS (~R R) P a (FBRel⊆FB ((~R R)) a (RisFBRel a)) (λ y Rya y∉P → no (y ,, Rya , y∉P)) λ H → a∉P (Rind a H)) 

  FB∧WDec→accCor : (~R R) isFB → R isDec → wdec (R -accessible) → accessibilityIsCoreductive R
  FB∧WDec→accCor RisFB RisDec wdecAcc = indP→CorP (dec∧FB→FBRel (~R R) RisDec RisFB) (R -accessible) wdecAcc λ x → acc  
  
  record CorSequence (P : 𝓟 A) (Pcor : R -coreductive P) : Set where
      constructor CS
      field
          init : Σ[ a ∈ A ] (a ∉ P)
      CorSeq : ℕ → Σ[ e ∈ A ] (e ∉ P)
      CorSeq zero = init
      CorSeq  (succ n) with CorSeq n
      ... | (a' ,, Ha') with Pcor a' Ha'
      ... | (x ,, Rxa , x∉P) = (x ,, x∉P)
      seq : (ℕ → A)
      seq = fst ∘ CorSeq
      seq⊆CP : ∀ (n : ℕ) → seq n ∈ (∁ P)
      seq⊆CP n = snd (CorSeq n)
      seq-inc : (R -decreasing) seq
      seq-inc n with CorSeq n
      ... | a ,, Ha with Pcor a Ha
      ... | (x ,, Rax , x∉P) = Rax
