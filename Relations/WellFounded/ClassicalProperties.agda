-- Classical properties required for WF implications 
open import Logic
open import Predicates
open import Relations.Core
open import Datatypes
open import Classical
open import Relations.Decidable
open import Relations.ClosureOperators
open import Relations.Seq
open import Relations.WellFounded.WFDefinitions
-- TODO: Remove unused imports
module Relations.WellFounded.ClassicalProperties {A : Set} (R : 𝓡 A) where

    AccCor : Set 
    AccCor = R -coreductive (R -accessible)

    AccDNE : Set
    AccDNE = ¬¬Closed (R -accessible)