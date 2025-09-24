-- We have a number of different definitions for WFCor, this file shows they are equivalent.
open import Logic
open import Predicates

open import Relations.WellFounded.WFDefinitions 
open import Relations.WellFounded.WFWeakDefinitions
module Relations.WellFounded.WFCoreductiveImplications {A : Set} (R : 𝓡 A) where
  open import Relations.Coreductive R
  isWFminCor→isWFCor¬¬ : R isWFminCor → R isWFcor¬¬
  isWFminCor→isWFCor¬¬ iwfc P Pco x ¬px with iwfc P Pco ¬px
  ... | (y ,, ¬py , ymin) with Pco y ¬py
  ... | (z ,, Rzy , ¬pz) = ymin z ¬pz Rzy

  Cor¬¬→isWFminCor : (∀ P → R -coreductive P → ∀ x → ¬¬ P x) → R isWFminCor
  Cor¬¬→isWFminCor H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFcor→isWFminCor : R isWFcor  → R isWFminCor
  isWFcor→isWFminCor RisWFcor = Cor¬¬→isWFminCor (λ P P∈Cor a → λ a∉P → a∉P (RisWFcor a P P∈Cor))

  isWFminCor+→isWFminCor : R isWFminCor+ → R isWFminCor
  isWFminCor+→isWFminCor RisWFminCor+ P Pcor a∉P with RisWFminCor+ P Pcor a∉P
  ... | (x ,, x∉P , H) = x ,, x∉P , λ y y∉P Ryx → y∉P (H y Ryx)

  isWFcor¬¬→isWFminCor+ : R isWFcor¬¬ → R isWFminCor+
  isWFcor¬¬→isWFminCor+ H P Pcor {a} a∉P = ∅ (H P Pcor a a∉P )

  isWFminCor→isWFminCor+ : R isWFminCor → R isWFminCor+
  isWFminCor→isWFminCor+ wfmc = isWFcor¬¬→isWFminCor+ (isWFminCor→isWFCor¬¬ wfmc )