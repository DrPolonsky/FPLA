open import Logic
open import Lifting 
open import LAM.Lambda
open import LAM.Reduction.Beta
open import LAM.Reduction.StandardBeta
open import LAM.Reduction.ParallelBeta
open import ARS.Properties 

module LAM.Reduction.ChurchRosser where 


CRbeta : ∀ {V : Set} → _⟶β_ {V} isCR
CRbeta {V} s {t1} {t2} st1 st2 
  with ⟶s\⇉⋆ (⟶β⋆⊆⟶s st1) (⟶β⋆⊆⇉⋆ st2) 
... | (u ,, t1u , t2u) = u ,, ⇉⋆⊆⟶β⋆ t1u , ⟶s⊆⟶β⋆ t2 u t2u

-- We get this for free by ARS
UNbeta : ∀ {V : Set} → _⟶β_ {V} isUN₌
UNbeta = Theorem-1-2-2.CR→UN CRbeta where open import ARS.Theorems


